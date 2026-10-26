import V185TrunkScan23Chunk1081

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6406149 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 1, 5, 2]
def baseStart_6406149 : Nat := 118140960795 + 6406149 * 2 ^ 59
def prefixEnd_6406149 : Nat := 4983230072969 + 3 ^ 40 * 6406149 * 2
def baseEnd_6406149 : Nat := 3289433581319561646276163

theorem tailTrace_6406149 : CollatzResearch.WordTrace tailWord_6406149 prefixEnd_6406149 3289433581319561646276163 := by
  unfold tailWord_6406149
  simp only [CollatzResearch.WordTrace]
  refine ⟨233651449268623730989901501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155767632845749153993267667 233651449268623730989901501)
  ·
    refine ⟨87619293475733899121213063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233651449268623730989901501 87619293475733899121213063)
    ·
      refine ⟨131428940213600848681819595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87619293475733899121213063 131428940213600848681819595)
      ·
        refine ⟨197143410320401273022729393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131428940213600848681819595 197143410320401273022729393)
        ·
          refine ⟨147857557740300954767047045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197143410320401273022729393 147857557740300954767047045)
          ·
            refine ⟨27723292076306429018821321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147857557740300954767047045 27723292076306429018821321)
            ·
              refine ⟨20792469057229821764115991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27723292076306429018821321 20792469057229821764115991)
              ·
                refine ⟨31188703585844732646173987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20792469057229821764115991 31188703585844732646173987)
                ·
                  refine ⟨46783055378767098969260981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31188703585844732646173987 46783055378767098969260981)
                  ·
                    refine ⟨4385911441759415528368217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46783055378767098969260981 4385911441759415528368217)
                    ·
                      refine ⟨3289433581319561646276163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385911441759415528368217 3289433581319561646276163)
                      ·
                        rfl

theorem cell23_6406149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_6406149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406149 prefixEnd_6406149 := by exact prefixLift 6406149
  have htrace : WordTrace (prefixWord ++ tailWord_6406149) baseStart_6406149 baseEnd_6406149 := by
    simpa [prefixWord, tailWord_6406149, baseEnd_6406149] using wordTrace_append hprefix tailTrace_6406149
  have hstable : (prefixWord ++ tailWord_6406149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406149).length < 2 ^ (prefixWord ++ tailWord_6406149).sum := by decide
  have hdescent : baseEnd_6406149 < baseStart_6406149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406173 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_6406173 : Nat := 118140960795 + 6406173 * 2 ^ 59
def prefixEnd_6406173 : Nat := 4983230072969 + 3 ^ 40 * 6406173 * 2
def baseEnd_6406173 : Nat := 3289445904855269552376053

theorem tailTrace_6406173 : CollatzResearch.WordTrace tailWord_6406173 prefixEnd_6406173 3289445904855269552376053 := by
  unfold tailWord_6406173
  simp only [CollatzResearch.WordTrace]
  refine ⟨233652324620536783088775173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155768216413691188725850115 233652324620536783088775173)
  ·
    refine ⟨43809810866350646829145345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233652324620536783088775173 43809810866350646829145345)
    ·
      refine ⟨32857358149762985121859009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43809810866350646829145345 32857358149762985121859009)
      ·
        refine ⟨24643018612322238841394257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32857358149762985121859009 24643018612322238841394257)
        ·
          refine ⟨18482263959241679131045693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24643018612322238841394257 18482263959241679131045693)
          ·
            refine ⟨6930848984715629674142135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18482263959241679131045693 6930848984715629674142135)
            ·
              refine ⟨10396273477073444511213203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930848984715629674142135 10396273477073444511213203)
              ·
                refine ⟨15594410215610166766819805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396273477073444511213203 15594410215610166766819805)
                ·
                  refine ⟨5847903830853812537557427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15594410215610166766819805 5847903830853812537557427)
                  ·
                    refine ⟨8771855746280718806336141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5847903830853812537557427 8771855746280718806336141)
                    ·
                      refine ⟨3289445904855269552376053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8771855746280718806336141 3289445904855269552376053)
                      ·
                        rfl

theorem cell23_6406173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_6406173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406173 prefixEnd_6406173 := by exact prefixLift 6406173
  have htrace : WordTrace (prefixWord ++ tailWord_6406173) baseStart_6406173 baseEnd_6406173 := by
    simpa [prefixWord, tailWord_6406173, baseEnd_6406173] using wordTrace_append hprefix tailTrace_6406173
  have hstable : (prefixWord ++ tailWord_6406173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406173).length < 2 ^ (prefixWord ++ tailWord_6406173).sum := by decide
  have hdescent : baseEnd_6406173 < baseStart_6406173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406192 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_6406192 : Nat := 118140960795 + 6406192 * 2 ^ 59
def prefixEnd_6406192 : Nat := 4983230072969 + 3 ^ 40 * 6406192 * 2
def baseEnd_6406192 : Nat := 3289455660987704978038465

theorem tailTrace_6406192 : CollatzResearch.WordTrace tailWord_6406192 prefixEnd_6406192 3289455660987704978038465 := by
  unfold tailWord_6406192
  simp only [CollatzResearch.WordTrace]
  refine ⟨116826508803733974666858415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155768678404978632889144553 116826508803733974666858415)
  ·
    refine ⟨175239763205600962000287623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116826508803733974666858415 175239763205600962000287623)
    ·
      refine ⟨262859644808401443000431435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175239763205600962000287623 262859644808401443000431435)
      ·
        refine ⟨394289467212602164500647153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262859644808401443000431435 394289467212602164500647153)
        ·
          refine ⟨295717100409451623375485365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394289467212602164500647153 295717100409451623375485365)
          ·
            refine ⟨27723478163386089691451753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295717100409451623375485365 27723478163386089691451753)
            ·
              refine ⟨20792608622539567268588815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27723478163386089691451753 20792608622539567268588815)
              ·
                refine ⟨31188912933809350902883223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20792608622539567268588815 31188912933809350902883223)
                ·
                  refine ⟨46783369400714026354324835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31188912933809350902883223 46783369400714026354324835)
                  ·
                    refine ⟨70175054101071039531487253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46783369400714026354324835 70175054101071039531487253)
                    ·
                      refine ⟨3289455660987704978038465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70175054101071039531487253 3289455660987704978038465)
                      ·
                        rfl

theorem cell23_6406192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_6406192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406192 prefixEnd_6406192 := by exact prefixLift 6406192
  have htrace : WordTrace (prefixWord ++ tailWord_6406192) baseStart_6406192 baseEnd_6406192 := by
    simpa [prefixWord, tailWord_6406192, baseEnd_6406192] using wordTrace_append hprefix tailTrace_6406192
  have hstable : (prefixWord ++ tailWord_6406192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406192).length < 2 ^ (prefixWord ++ tailWord_6406192).sum := by decide
  have hdescent : baseEnd_6406192 < baseStart_6406192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406206 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_6406206 : Nat := 118140960795 + 6406206 * 2 ^ 59
def prefixEnd_6406206 : Nat := 4983230072969 + 3 ^ 40 * 6406206 * 2
def baseEnd_6406206 : Nat := 1096487616572289307754467

theorem tailTrace_6406206 : CollatzResearch.WordTrace tailWord_6406206 prefixEnd_6406206 1096487616572289307754467 := by
  unfold tailWord_6406206
  simp only [CollatzResearch.WordTrace]
  refine ⟨29206691028677153715590809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155769018819611486483150981 29206691028677153715590809)
  ·
    refine ⟨21905018271507865286693107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29206691028677153715590809 21905018271507865286693107)
    ·
      refine ⟨32857527407261797930039661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21905018271507865286693107 32857527407261797930039661)
      ·
        refine ⟨12321572777723174223764873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32857527407261797930039661 12321572777723174223764873)
        ·
          refine ⟨9241179583292380667823655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12321572777723174223764873 9241179583292380667823655)
          ·
            refine ⟨13861769374938571001735483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241179583292380667823655 13861769374938571001735483)
            ·
              refine ⟨20792654062407856502603225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13861769374938571001735483 20792654062407856502603225)
              ·
                refine ⟨15594490546805892376952419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20792654062407856502603225 15594490546805892376952419)
                ·
                  refine ⟨23391735820208838565428629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15594490546805892376952419 23391735820208838565428629)
                  ·
                    refine ⟨1096487616572289307754467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23391735820208838565428629 1096487616572289307754467)
                    ·
                      rfl

theorem cell23_6406206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_6406206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406206 prefixEnd_6406206 := by exact prefixLift 6406206
  have htrace : WordTrace (prefixWord ++ tailWord_6406206) baseStart_6406206 baseEnd_6406206 := by
    simpa [prefixWord, tailWord_6406206, baseEnd_6406206] using wordTrace_append hprefix tailTrace_6406206
  have hstable : (prefixWord ++ tailWord_6406206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406206).length < 2 ^ (prefixWord ++ tailWord_6406206).sum := by decide
  have hdescent : baseEnd_6406206 < baseStart_6406206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406209 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6406209 : Nat := 118140960795 + 6406209 * 2 ^ 59
def prefixEnd_6406209 : Nat := 4983230072969 + 3 ^ 40 * 6406209 * 2
def baseEnd_6406209 : Nat := 3289464390158831411525887

theorem tailTrace_6406209 : CollatzResearch.WordTrace tailWord_6406209 prefixEnd_6406209 3289464390158831411525887 := by
  unfold tailWord_6406209
  simp only [CollatzResearch.WordTrace]
  refine ⟨233653637648406361237085681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155769091765604240824723787 233653637648406361237085681)
  ·
    refine ⟨175240228236304770927814261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233653637648406361237085681 175240228236304770927814261)
    ·
      refine ⟨16428771397153572274482587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175240228236304770927814261 16428771397153572274482587)
      ·
        refine ⟨24643157095730358411723881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16428771397153572274482587 24643157095730358411723881)
        ·
          refine ⟨18482367821797768808792911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24643157095730358411723881 18482367821797768808792911)
          ·
            refine ⟨27723551732696653213189367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18482367821797768808792911 27723551732696653213189367)
            ·
              refine ⟨41585327599044979819784051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27723551732696653213189367 41585327599044979819784051)
              ·
                refine ⟨62377991398567469729676077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41585327599044979819784051 62377991398567469729676077)
                ·
                  refine ⟨23391746774462801148628529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62377991398567469729676077 23391746774462801148628529)
                  ·
                    refine ⟨17543810080847100861471397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23391746774462801148628529 17543810080847100861471397)
                    ·
                      refine ⟨3289464390158831411525887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17543810080847100861471397 3289464390158831411525887)
                      ·
                        rfl

theorem cell23_6406209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6406209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406209 prefixEnd_6406209 := by exact prefixLift 6406209
  have htrace : WordTrace (prefixWord ++ tailWord_6406209) baseStart_6406209 baseEnd_6406209 := by
    simpa [prefixWord, tailWord_6406209, baseEnd_6406209] using wordTrace_append hprefix tailTrace_6406209
  have hstable : (prefixWord ++ tailWord_6406209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406209).length < 2 ^ (prefixWord ++ tailWord_6406209).sum := by decide
  have hdescent : baseEnd_6406209 < baseStart_6406209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406213 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 1, 2, 2]
def baseStart_6406213 : Nat := 118140960795 + 6406213 * 2 ^ 59
def prefixEnd_6406213 : Nat := 4983230072969 + 3 ^ 40 * 6406213 * 2
def baseEnd_6406213 : Nat := 3289466444081449395875869

theorem tailTrace_6406213 : CollatzResearch.WordTrace tailWord_6406213 prefixEnd_6406213 3289466444081449395875869 := by
  unfold tailWord_6406213
  simp only [CollatzResearch.WordTrace]
  refine ⟨233653783540391869920231293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155769189026927913280154195 233653783540391869920231293)
  ·
    refine ⟨87620168827646951220086735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233653783540391869920231293 87620168827646951220086735)
    ·
      refine ⟨131430253241470426830130103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87620168827646951220086735 131430253241470426830130103)
      ·
        refine ⟨197145379862205640245195155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131430253241470426830130103 197145379862205640245195155)
        ·
          refine ⟨295718069793308460367792733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197145379862205640245195155 295718069793308460367792733)
          ·
            refine ⟨110894276172490672637922275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295718069793308460367792733 110894276172490672637922275)
            ·
              refine ⟨166341414258736008956883413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110894276172490672637922275 166341414258736008956883413)
              ·
                refine ⟨3898626896689125209926955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166341414258736008956883413 3898626896689125209926955)
                ·
                  refine ⟨5847940345033687814890433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898626896689125209926955 5847940345033687814890433)
                  ·
                    refine ⟨4385955258775265861167825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847940345033687814890433 4385955258775265861167825)
                    ·
                      refine ⟨3289466444081449395875869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385955258775265861167825 3289466444081449395875869)
                      ·
                        rfl

theorem cell23_6406213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_6406213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406213 prefixEnd_6406213 := by exact prefixLift 6406213
  have htrace : WordTrace (prefixWord ++ tailWord_6406213) baseStart_6406213 baseEnd_6406213 := by
    simpa [prefixWord, tailWord_6406213, baseEnd_6406213] using wordTrace_append hprefix tailTrace_6406213
  have hstable : (prefixWord ++ tailWord_6406213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406213).length < 2 ^ (prefixWord ++ tailWord_6406213).sum := by decide
  have hdescent : baseEnd_6406213 < baseStart_6406213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406232 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_6406232 : Nat := 118140960795 + 6406232 * 2 ^ 59
def prefixEnd_6406232 : Nat := 4983230072969 + 3 ^ 40 * 6406232 * 2
def baseEnd_6406232 : Nat := 1096492066737961607179427

theorem tailTrace_6406232 : CollatzResearch.WordTrace tailWord_6406232 prefixEnd_6406232 1096492066737961607179427 := by
  unfold tailWord_6406232
  simp only [CollatzResearch.WordTrace]
  refine ⟨116827238263661518082586475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155769651018215357443448633 116827238263661518082586475)
  ·
    refine ⟨175240857395492277123879713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116827238263661518082586475 175240857395492277123879713)
    ·
      refine ⟨131430643046619207842909785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175240857395492277123879713 131430643046619207842909785)
      ·
        refine ⟨98572982284964405882182339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131430643046619207842909785 98572982284964405882182339)
        ·
          refine ⟨147859473427446608823273509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98572982284964405882182339 147859473427446608823273509)
          ·
            refine ⟨27723651267646239154363783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147859473427446608823273509 27723651267646239154363783)
            ·
              refine ⟨41585476901469358731545675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27723651267646239154363783 41585476901469358731545675)
              ·
                refine ⟨62378215352204038097318513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41585476901469358731545675 62378215352204038097318513)
                ·
                  refine ⟨46783661514153028572988885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62378215352204038097318513 46783661514153028572988885)
                  ·
                    refine ⟨1096492066737961607179427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46783661514153028572988885 1096492066737961607179427)
                    ·
                      rfl

theorem cell23_6406232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_6406232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406232 prefixEnd_6406232 := by exact prefixLift 6406232
  have htrace : WordTrace (prefixWord ++ tailWord_6406232) baseStart_6406232 baseEnd_6406232 := by
    simpa [prefixWord, tailWord_6406232, baseEnd_6406232] using wordTrace_append hprefix tailTrace_6406232
  have hstable : (prefixWord ++ tailWord_6406232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406232).length < 2 ^ (prefixWord ++ tailWord_6406232).sum := by decide
  have hdescent : baseEnd_6406232 < baseStart_6406232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406256 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 3, 3, 2]
def baseStart_6406256 : Nat := 118140960795 + 6406256 * 2 ^ 59
def prefixEnd_6406256 : Nat := 4983230072969 + 3 ^ 40 * 6406256 * 2
def baseEnd_6406256 : Nat := 3289488523749592727638171

theorem tailTrace_6406256 : CollatzResearch.WordTrace tailWord_6406256 prefixEnd_6406256 3289488523749592727638171 := by
  unfold tailWord_6406256
  simp only [CollatzResearch.WordTrace]
  refine ⟨116827675939618044132023311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155770234586157392176031081 116827675939618044132023311)
  ·
    refine ⟨175241513909427066198034967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116827675939618044132023311 175241513909427066198034967)
    ·
      refine ⟨262862270864140599297052451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175241513909427066198034967 262862270864140599297052451)
      ·
        refine ⟨394293406296210898945578677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262862270864140599297052451 394293406296210898945578677)
        ·
          refine ⟨36965006840269771776148001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 394293406296210898945578677 36965006840269771776148001)
          ·
            refine ⟨27723755130202328832111001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36965006840269771776148001 27723755130202328832111001)
            ·
              refine ⟨20792816347651746624083251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27723755130202328832111001 20792816347651746624083251)
              ·
                refine ⟨31189224521477619936124877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20792816347651746624083251 31189224521477619936124877)
                ·
                  refine ⟨11695959195554107476046829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31189224521477619936124877 11695959195554107476046829)
                  ·
                    refine ⟨4385984698332790303517561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11695959195554107476046829 4385984698332790303517561)
                    ·
                      refine ⟨3289488523749592727638171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4385984698332790303517561 3289488523749592727638171)
                      ·
                        rfl

theorem cell23_6406256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 3, 2].length) (baseStart_6406256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406256 prefixEnd_6406256 := by exact prefixLift 6406256
  have htrace : WordTrace (prefixWord ++ tailWord_6406256) baseStart_6406256 baseEnd_6406256 := by
    simpa [prefixWord, tailWord_6406256, baseEnd_6406256] using wordTrace_append hprefix tailTrace_6406256
  have hstable : (prefixWord ++ tailWord_6406256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406256).length < 2 ^ (prefixWord ++ tailWord_6406256).sum := by decide
  have hdescent : baseEnd_6406256 < baseStart_6406256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406272 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_6406272 : Nat := 118140960795 + 6406272 * 2 ^ 59
def prefixEnd_6406272 : Nat := 4983230072969 + 3 ^ 40 * 6406272 * 2
def baseEnd_6406272 : Nat := 3289496739440064665038097

theorem tailTrace_6406272 : CollatzResearch.WordTrace tailWord_6406272 prefixEnd_6406272 3289496739440064665038097 := by
  unfold tailWord_6406272
  simp only [CollatzResearch.WordTrace]
  refine ⟨116827967723589061498314535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155770623631452081997752713 116827967723589061498314535)
  ·
    refine ⟨175241951585383592247471803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116827967723589061498314535 175241951585383592247471803)
    ·
      refine ⟨262862927378075388371207705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175241951585383592247471803 262862927378075388371207705)
      ·
        refine ⟨197147195533556541278405779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262862927378075388371207705 197147195533556541278405779)
        ·
          refine ⟨295720793300334811917608669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197147195533556541278405779 295720793300334811917608669)
          ·
            refine ⟨110895297487625554469103251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295720793300334811917608669 110895297487625554469103251)
            ·
              refine ⟨166342946231438331703654877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110895297487625554469103251 166342946231438331703654877)
              ·
                refine ⟨62378604836789374388870579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166342946231438331703654877 62378604836789374388870579)
                ·
                  refine ⟨93567907255184061583305869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62378604836789374388870579 93567907255184061583305869)
                  ·
                    refine ⟨35087965220694023093739701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93567907255184061583305869 35087965220694023093739701)
                    ·
                      refine ⟨3289496739440064665038097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35087965220694023093739701 3289496739440064665038097)
                      ·
                        rfl

theorem cell23_6406272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_6406272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406272 prefixEnd_6406272 := by exact prefixLift 6406272
  have htrace : WordTrace (prefixWord ++ tailWord_6406272) baseStart_6406272 baseEnd_6406272 := by
    simpa [prefixWord, tailWord_6406272, baseEnd_6406272] using wordTrace_append hprefix tailTrace_6406272
  have hstable : (prefixWord ++ tailWord_6406272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406272).length < 2 ^ (prefixWord ++ tailWord_6406272).sum := by decide
  have hdescent : baseEnd_6406272 < baseStart_6406272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406280 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6406280 : Nat := 118140960795 + 6406280 * 2 ^ 59
def prefixEnd_6406280 : Nat := 4983230072969 + 3 ^ 40 * 6406280 * 2
def baseEnd_6406280 : Nat := 3289500847285300633738061

theorem tailTrace_6406280 : CollatzResearch.WordTrace tailWord_6406280 prefixEnd_6406280 3289500847285300633738061 := by
  unfold tailWord_6406280
  simp only [CollatzResearch.WordTrace]
  refine ⟨116828113615574570181460147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155770818154099426908613529 116828113615574570181460147)
  ·
    refine ⟨175242170423361855272190221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116828113615574570181460147 175242170423361855272190221)
    ·
      refine ⟨65715813908760695727071333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175242170423361855272190221 65715813908760695727071333)
      ·
        refine ⟨12321715107892630448825875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65715813908760695727071333 12321715107892630448825875)
        ·
          refine ⟨18482572661838945673238813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12321715107892630448825875 18482572661838945673238813)
          ·
            refine ⟨6930964748189604627464555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18482572661838945673238813 6930964748189604627464555)
            ·
              refine ⟨10396447122284406941196833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930964748189604627464555 10396447122284406941196833)
              ·
                refine ⟨7797335341713305205897625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10396447122284406941196833 7797335341713305205897625)
                ·
                  refine ⟨5848001506284978904423219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7797335341713305205897625 5848001506284978904423219)
                  ·
                    refine ⟨8772002259427468356634829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5848001506284978904423219 8772002259427468356634829)
                    ·
                      refine ⟨3289500847285300633738061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772002259427468356634829 3289500847285300633738061)
                      ·
                        rfl

theorem cell23_6406280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6406280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406280 prefixEnd_6406280 := by exact prefixLift 6406280
  have htrace : WordTrace (prefixWord ++ tailWord_6406280) baseStart_6406280 baseEnd_6406280 := by
    simpa [prefixWord, tailWord_6406280, baseEnd_6406280] using wordTrace_append hprefix tailTrace_6406280
  have hstable : (prefixWord ++ tailWord_6406280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406280).length < 2 ^ (prefixWord ++ tailWord_6406280).sum := by decide
  have hdescent : baseEnd_6406280 < baseStart_6406280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406294 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6406294 : Nat := 118140960795 + 6406294 * 2 ^ 59
def prefixEnd_6406294 : Nat := 4983230072969 + 3 ^ 40 * 6406294 * 2
def baseEnd_6406294 : Nat := 3289508036014463578962997

theorem tailTrace_6406294 : CollatzResearch.WordTrace tailWord_6406294 prefixEnd_6406294 3289508036014463578962997 := by
  unfold tailWord_6406294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603546115818651297120621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155771158568732280502619957 14603546115818651297120621)
  ·
    refine ⟨5476329793431994236420233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14603546115818651297120621 5476329793431994236420233)
    ·
      refine ⟨4107247345073995677315175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5476329793431994236420233 4107247345073995677315175)
      ·
        refine ⟨6160871017610993515972763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107247345073995677315175 6160871017610993515972763)
        ·
          refine ⟨9241306526416490273959145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160871017610993515972763 9241306526416490273959145)
          ·
            refine ⟨6930979894812367705469359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9241306526416490273959145 6930979894812367705469359)
            ·
              refine ⟨10396469842218551558204039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930979894812367705469359 10396469842218551558204039)
              ·
                refine ⟨15594704763327827337306059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396469842218551558204039 15594704763327827337306059)
                ·
                  refine ⟨23392057144991741005959089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15594704763327827337306059 23392057144991741005959089)
                  ·
                    refine ⟨17544042858743805754469317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23392057144991741005959089 17544042858743805754469317)
                    ·
                      refine ⟨3289508036014463578962997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17544042858743805754469317 3289508036014463578962997)
                      ·
                        rfl

theorem cell23_6406294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6406294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406294 prefixEnd_6406294 := by exact prefixLift 6406294
  have htrace : WordTrace (prefixWord ++ tailWord_6406294) baseStart_6406294 baseEnd_6406294 := by
    simpa [prefixWord, tailWord_6406294, baseEnd_6406294] using wordTrace_append hprefix tailTrace_6406294
  have hstable : (prefixWord ++ tailWord_6406294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406294).length < 2 ^ (prefixWord ++ tailWord_6406294).sum := by decide
  have hdescent : baseEnd_6406294 < baseStart_6406294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406303 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6406303 : Nat := 118140960795 + 6406303 * 2 ^ 59
def prefixEnd_6406303 : Nat := 4983230072969 + 3 ^ 40 * 6406303 * 2
def baseEnd_6406303 : Nat := 3289512657340354043750455

theorem tailTrace_6406303 : CollatzResearch.WordTrace tailWord_6406303 prefixEnd_6406303 3289512657340354043750455 := by
  unfold tailWord_6406303
  simp only [CollatzResearch.WordTrace]
  refine ⟨233657066110065815291007563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155771377406710543527338375 233657066110065815291007563)
  ·
    refine ⟨350485599165098722936511345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233657066110065815291007563 350485599165098722936511345)
    ·
      refine ⟨262864199373824042202383509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350485599165098722936511345 262864199373824042202383509)
      ·
        refine ⟨12321759345648001978236727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 262864199373824042202383509 12321759345648001978236727)
        ·
          refine ⟨18482639018472002967355091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12321759345648001978236727 18482639018472002967355091)
          ·
            refine ⟨27723958527708004451032637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18482639018472002967355091 27723958527708004451032637)
            ·
              refine ⟨10396484447890501669137239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27723958527708004451032637 10396484447890501669137239)
              ·
                refine ⟨15594726671835752503705859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396484447890501669137239 15594726671835752503705859)
                ·
                  refine ⟨23392090007753628755558789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15594726671835752503705859 23392090007753628755558789)
                  ·
                    refine ⟨4386016876453805391667273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23392090007753628755558789 4386016876453805391667273)
                    ·
                      refine ⟨3289512657340354043750455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386016876453805391667273 3289512657340354043750455)
                      ·
                        rfl

theorem cell23_6406303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6406303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406303 prefixEnd_6406303 := by exact prefixLift 6406303
  have htrace : WordTrace (prefixWord ++ tailWord_6406303) baseStart_6406303 baseEnd_6406303 := by
    simpa [prefixWord, tailWord_6406303, baseEnd_6406303] using wordTrace_append hprefix tailTrace_6406303
  have hstable : (prefixWord ++ tailWord_6406303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406303).length < 2 ^ (prefixWord ++ tailWord_6406303).sum := by decide
  have hdescent : baseEnd_6406303 < baseStart_6406303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406346 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_6406346 : Nat := 118140960795 + 6406346 * 2 ^ 59
def prefixEnd_6406346 : Nat := 4983230072969 + 3 ^ 40 * 6406346 * 2
def baseEnd_6406346 : Nat := 3289534737008497375512757

theorem tailTrace_6406346 : CollatzResearch.WordTrace tailWord_6406346 prefixEnd_6406346 3289534737008497375512757 := by
  unfold tailWord_6406346
  simp only [CollatzResearch.WordTrace]
  refine ⟨58414658612227508408705723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155772422965940022423215261 58414658612227508408705723)
  ·
    refine ⟨87621987918341262613058585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58414658612227508408705723 87621987918341262613058585)
    ·
      refine ⟨65716490938755946959793939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87621987918341262613058585 65716490938755946959793939)
      ·
        refine ⟨98574736408133920439690909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65716490938755946959793939 98574736408133920439690909)
        ·
          refine ⟨36965526153050220164884091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98574736408133920439690909 36965526153050220164884091)
          ·
            refine ⟨55448289229575330247326137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36965526153050220164884091 55448289229575330247326137)
            ·
              refine ⟨41586216922181497685494603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55448289229575330247326137 41586216922181497685494603)
              ·
                refine ⟨62379325383272246528241905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41586216922181497685494603 62379325383272246528241905)
                ·
                  refine ⟨46784494037454184896181429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62379325383272246528241905 46784494037454184896181429)
                  ·
                    refine ⟨4386046316011329834017009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46784494037454184896181429 4386046316011329834017009)
                    ·
                      refine ⟨3289534737008497375512757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386046316011329834017009 3289534737008497375512757)
                      ·
                        rfl

theorem cell23_6406346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_6406346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406346 prefixEnd_6406346 := by exact prefixLift 6406346
  have htrace : WordTrace (prefixWord ++ tailWord_6406346) baseStart_6406346 baseEnd_6406346 := by
    simpa [prefixWord, tailWord_6406346, baseEnd_6406346] using wordTrace_append hprefix tailTrace_6406346
  have hstable : (prefixWord ++ tailWord_6406346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406346).length < 2 ^ (prefixWord ++ tailWord_6406346).sum := by decide
  have hdescent : baseEnd_6406346 < baseStart_6406346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406359 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_6406359 : Nat := 118140960795 + 6406359 * 2 ^ 59
def prefixEnd_6406359 : Nat := 4983230072969 + 3 ^ 40 * 6406359 * 2
def baseEnd_6406359 : Nat := 3289541412257005824650197

theorem tailTrace_6406359 : CollatzResearch.WordTrace tailWord_6406359 prefixEnd_6406359 3289541412257005824650197 := by
  unfold tailWord_6406359
  simp only [CollatzResearch.WordTrace]
  refine ⟨233659108597862936855046131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155772739065241957903364087 233659108597862936855046131)
  ·
    refine ⟨350488662896794405282569197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233659108597862936855046131 350488662896794405282569197)
    ·
      refine ⟨131433248586297901980963449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350488662896794405282569197 131433248586297901980963449)
      ·
        refine ⟨98574936439723426485722587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131433248586297901980963449 98574936439723426485722587)
        ·
          refine ⟨147862404659585139728583881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98574936439723426485722587 147862404659585139728583881)
          ·
            refine ⟨110896803494688854796437911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147862404659585139728583881 110896803494688854796437911)
            ·
              refine ⟨166345205242033282194656867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110896803494688854796437911 166345205242033282194656867)
              ·
                refine ⟨249517807863049923291985301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166345205242033282194656867 249517807863049923291985301)
                ·
                  refine ⟨11696147243580465154311811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249517807863049923291985301 11696147243580465154311811)
                  ·
                    refine ⟨17544220865370697731467717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11696147243580465154311811 17544220865370697731467717)
                    ·
                      refine ⟨3289541412257005824650197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17544220865370697731467717 3289541412257005824650197)
                      ·
                        rfl

theorem cell23_6406359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_6406359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406359 prefixEnd_6406359 := by exact prefixLift 6406359
  have htrace : WordTrace (prefixWord ++ tailWord_6406359) baseStart_6406359 baseEnd_6406359 := by
    simpa [prefixWord, tailWord_6406359, baseEnd_6406359] using wordTrace_append hprefix tailTrace_6406359
  have hstable : (prefixWord ++ tailWord_6406359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406359).length < 2 ^ (prefixWord ++ tailWord_6406359).sum := by decide
  have hdescent : baseEnd_6406359 < baseStart_6406359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406376 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6406376 : Nat := 118140960795 + 6406376 * 2 ^ 59
def prefixEnd_6406376 : Nat := 4983230072969 + 3 ^ 40 * 6406376 * 2
def baseEnd_6406376 : Nat := 3289550141428132258137619

theorem tailTrace_6406376 : CollatzResearch.WordTrace tailWord_6406376 prefixEnd_6406376 3289550141428132258137619 := by
  unfold tailWord_6406376
  simp only [CollatzResearch.WordTrace]
  refine ⟨116829864319400674379207491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155773152425867565838943321 116829864319400674379207491)
  ·
    refine ⟨175244796479101011568811237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116829864319400674379207491 175244796479101011568811237)
    ·
      refine ⟨32858399339831439669152107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175244796479101011568811237 32858399339831439669152107)
      ·
        refine ⟨49287599009747159503728161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32858399339831439669152107 49287599009747159503728161)
        ·
          refine ⟨36965699257310369627796121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49287599009747159503728161 36965699257310369627796121)
          ·
            refine ⟨27724274442982777220847091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36965699257310369627796121 27724274442982777220847091)
            ·
              refine ⟨41586411664474165831270637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27724274442982777220847091 41586411664474165831270637)
              ·
                refine ⟨15594904374177812186726489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41586411664474165831270637 15594904374177812186726489)
                ·
                  refine ⟨11696178280633359140044867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15594904374177812186726489 11696178280633359140044867)
                  ·
                    refine ⟨17544267420950038710067301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11696178280633359140044867 17544267420950038710067301)
                    ·
                      refine ⟨3289550141428132258137619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17544267420950038710067301 3289550141428132258137619)
                      ·
                        rfl

theorem cell23_6406376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6406376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406376 prefixEnd_6406376 := by exact prefixLift 6406376
  have htrace : WordTrace (prefixWord ++ tailWord_6406376) baseStart_6406376 baseEnd_6406376 := by
    simpa [prefixWord, tailWord_6406376, baseEnd_6406376] using wordTrace_append hprefix tailTrace_6406376
  have hstable : (prefixWord ++ tailWord_6406376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406376).length < 2 ^ (prefixWord ++ tailWord_6406376).sum := by decide
  have hdescent : baseEnd_6406376 < baseStart_6406376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406403 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 1, 4]
def baseStart_6406403 : Nat := 118140960795 + 6406403 * 2 ^ 59
def prefixEnd_6406403 : Nat := 4983230072969 + 3 ^ 40 * 6406403 * 2
def baseEnd_6406403 : Nat := 1096521335135267884166665

theorem tailTrace_6406403 : CollatzResearch.WordTrace tailWord_6406403 prefixEnd_6406403 1096521335135267884166665 := by
  unfold tailWord_6406403
  simp only [CollatzResearch.WordTrace]
  refine ⟨233660713409703532369647863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155773808939802354913098575 233660713409703532369647863)
  ·
    refine ⟨350491070114555298554471795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233660713409703532369647863 350491070114555298554471795)
    ·
      refine ⟨525736605171832947831707693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350491070114555298554471795 525736605171832947831707693)
      ·
        refine ⟨197151226939437355436890385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525736605171832947831707693 197151226939437355436890385)
        ·
          refine ⟨147863420204578016577667789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197151226939437355436890385 147863420204578016577667789)
          ·
            refine ⟨55448782576716756216625421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147863420204578016577667789 55448782576716756216625421)
            ·
              refine ⟨20793293466268783581234533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55448782576716756216625421 20793293466268783581234533)
              ·
                refine ⟨3898742524925396921481475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20793293466268783581234533 3898742524925396921481475)
                ·
                  refine ⟨5848113787388095382222213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898742524925396921481475 5848113787388095382222213)
                  ·
                    refine ⟨1096521335135267884166665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848113787388095382222213 1096521335135267884166665)
                    ·
                      rfl

theorem cell23_6406403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 4].length) (baseStart_6406403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406403 prefixEnd_6406403 := by exact prefixLift 6406403
  have htrace : WordTrace (prefixWord ++ tailWord_6406403) baseStart_6406403 baseEnd_6406403 := by
    simpa [prefixWord, tailWord_6406403, baseEnd_6406403] using wordTrace_append hprefix tailTrace_6406403
  have hstable : (prefixWord ++ tailWord_6406403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406403).length < 2 ^ (prefixWord ++ tailWord_6406403).sum := by decide
  have hdescent : baseEnd_6406403 < baseStart_6406403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406430 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6406430 : Nat := 118140960795 + 6406430 * 2 ^ 59
def prefixEnd_6406430 : Nat := 4983230072969 + 3 ^ 40 * 6406430 * 2
def baseEnd_6406430 : Nat := 3289577869383475046862371

theorem tailTrace_6406430 : CollatzResearch.WordTrace tailWord_6406430 prefixEnd_6406430 3289577869383475046862371 := by
  unfold tailWord_6406430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29207712272575714497610093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155774465453737143987253829 29207712272575714497610093)
  ·
    refine ⟨10952892102215892936603785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29207712272575714497610093 10952892102215892936603785)
    ·
      refine ⟨8214669076661919702452839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10952892102215892936603785 8214669076661919702452839)
      ·
        refine ⟨12322003614992879553679259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8214669076661919702452839 12322003614992879553679259)
        ·
          refine ⟨18483005422489319330518889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322003614992879553679259 18483005422489319330518889)
          ·
            refine ⟨13862254066866989497889167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18483005422489319330518889 13862254066866989497889167)
            ·
              refine ⟨20793381100300484246833751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13862254066866989497889167 20793381100300484246833751)
              ·
                refine ⟨31190071650450726370250627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20793381100300484246833751 31190071650450726370250627)
                ·
                  refine ⟨46785107475676089555375941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31190071650450726370250627 46785107475676089555375941)
                  ·
                    refine ⟨8772207651689266791632989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46785107475676089555375941 8772207651689266791632989)
                    ·
                      refine ⟨3289577869383475046862371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772207651689266791632989 3289577869383475046862371)
                      ·
                        rfl

theorem cell23_6406430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6406430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406430 prefixEnd_6406430 := by exact prefixLift 6406430
  have htrace : WordTrace (prefixWord ++ tailWord_6406430) baseStart_6406430 baseEnd_6406430 := by
    simpa [prefixWord, tailWord_6406430, baseEnd_6406430] using wordTrace_append hprefix tailTrace_6406430
  have hstable : (prefixWord ++ tailWord_6406430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406430).length < 2 ^ (prefixWord ++ tailWord_6406430).sum := by decide
  have hdescent : baseEnd_6406430 < baseStart_6406430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406450 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_6406450 : Nat := 118140960795 + 6406450 * 2 ^ 59
def prefixEnd_6406450 : Nat := 4983230072969 + 3 ^ 40 * 6406450 * 2
def baseEnd_6406450 : Nat := 365509793221840552068031

theorem tailTrace_6406450 : CollatzResearch.WordTrace tailWord_6406450 prefixEnd_6406450 365509793221840552068031 := by
  unfold tailWord_6406450
  simp only [CollatzResearch.WordTrace]
  refine ⟨58415606910133314849152201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155774951760355506264405869 58415606910133314849152201)
  ·
    refine ⟨43811705182599986136864151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58415606910133314849152201 43811705182599986136864151)
    ·
      refine ⟨65717557773899979205296227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43811705182599986136864151 65717557773899979205296227)
      ·
        refine ⟨98576336660849968807944341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65717557773899979205296227 98576336660849968807944341)
        ·
          refine ⟨4620765780977342287872391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98576336660849968807944341 4620765780977342287872391)
          ·
            refine ⟨6931148671466013431808587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4620765780977342287872391 6931148671466013431808587)
            ·
              refine ⟨10396723007199020147712881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931148671466013431808587 10396723007199020147712881)
              ·
                refine ⟨7797542255399265110784661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10396723007199020147712881 7797542255399265110784661)
                ·
                  refine ⟨365509793221840552068031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7797542255399265110784661 365509793221840552068031)
                  ·
                    rfl

theorem cell23_6406450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_6406450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406450 prefixEnd_6406450 := by exact prefixLift 6406450
  have htrace : WordTrace (prefixWord ++ tailWord_6406450) baseStart_6406450 baseEnd_6406450 := by
    simpa [prefixWord, tailWord_6406450, baseEnd_6406450] using wordTrace_append hprefix tailTrace_6406450
  have hstable : (prefixWord ++ tailWord_6406450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406450).length < 2 ^ (prefixWord ++ tailWord_6406450).sum := by decide
  have hdescent : baseEnd_6406450 < baseStart_6406450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406453 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_6406453 : Nat := 118140960795 + 6406453 * 2 ^ 59
def prefixEnd_6406453 : Nat := 4983230072969 + 3 ^ 40 * 6406453 * 2
def baseEnd_6406453 : Nat := 3289589679438528456874765

theorem tailTrace_6406453 : CollatzResearch.WordTrace tailWord_6406453 prefixEnd_6406453 3289589679438528456874765 := by
  unfold tailWord_6406453
  simp only [CollatzResearch.WordTrace]
  refine ⟨233662537059522390908968013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155775024706348260605978675 233662537059522390908968013)
  ·
    refine ⟨87623451397320896590863005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233662537059522390908968013 87623451397320896590863005)
    ·
      refine ⟨32858794273995336221573627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87623451397320896590863005 32858794273995336221573627)
      ·
        refine ⟨49288191410993004332360441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32858794273995336221573627 49288191410993004332360441)
        ·
          refine ⟨36966143558244753249270331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49288191410993004332360441 36966143558244753249270331)
          ·
            refine ⟨55449215337367129873905497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36966143558244753249270331 55449215337367129873905497)
            ·
              refine ⟨41586911503025347405429123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55449215337367129873905497 41586911503025347405429123)
              ·
                refine ⟨62380367254538021108143685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41586911503025347405429123 62380367254538021108143685)
                ·
                  refine ⟨11696318860225878957776941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62380367254538021108143685 11696318860225878957776941)
                  ·
                    refine ⟨4386119572584704609166353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11696318860225878957776941 4386119572584704609166353)
                    ·
                      refine ⟨3289589679438528456874765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386119572584704609166353 3289589679438528456874765)
                      ·
                        rfl

theorem cell23_6406453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_6406453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406453 prefixEnd_6406453 := by exact prefixLift 6406453
  have htrace : WordTrace (prefixWord ++ tailWord_6406453) baseStart_6406453 baseEnd_6406453 := by
    simpa [prefixWord, tailWord_6406453, baseEnd_6406453] using wordTrace_append hprefix tailTrace_6406453
  have hstable : (prefixWord ++ tailWord_6406453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406453).length < 2 ^ (prefixWord ++ tailWord_6406453).sum := by decide
  have hdescent : baseEnd_6406453 < baseStart_6406453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406460 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_6406460 : Nat := 118140960795 + 6406460 * 2 ^ 59
def prefixEnd_6406460 : Nat := 4983230072969 + 3 ^ 40 * 6406460 * 2
def baseEnd_6406460 : Nat := 3289593273803109929487233

theorem tailTrace_6406460 : CollatzResearch.WordTrace tailWord_6406460 prefixEnd_6406460 3289593273803109929487233 := by
  unfold tailWord_6406460
  simp only [CollatzResearch.WordTrace]
  refine ⟨116831396185248515552236417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155775194913664687402981889 116831396185248515552236417)
  ·
    refine ⟨87623547138936386664177313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116831396185248515552236417 87623547138936386664177313)
    ·
      refine ⟨65717660354202289998132985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87623547138936386664177313 65717660354202289998132985)
      ·
        refine ⟨49288245265651717498599739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65717660354202289998132985 49288245265651717498599739)
        ·
          refine ⟨73932367898477576247899609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49288245265651717498599739 73932367898477576247899609)
          ·
            refine ⟨55449275923858182185924707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73932367898477576247899609 55449275923858182185924707)
            ·
              refine ⟨83173913885787273278887061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55449275923858182185924707 83173913885787273278887061)
              ·
                refine ⟨3898777213396278434947831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83173913885787273278887061 3898777213396278434947831)
                ·
                  refine ⟨5848165820094417652421747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898777213396278434947831 5848165820094417652421747)
                  ·
                    refine ⟨8772248730141626478632621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5848165820094417652421747 8772248730141626478632621)
                    ·
                      refine ⟨3289593273803109929487233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772248730141626478632621 3289593273803109929487233)
                      ·
                        rfl

theorem cell23_6406460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_6406460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406460 prefixEnd_6406460 := by exact prefixLift 6406460
  have htrace : WordTrace (prefixWord ++ tailWord_6406460) baseStart_6406460 baseEnd_6406460 := by
    simpa [prefixWord, tailWord_6406460, baseEnd_6406460] using wordTrace_append hprefix tailTrace_6406460
  have hstable : (prefixWord ++ tailWord_6406460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406460).length < 2 ^ (prefixWord ++ tailWord_6406460).sum := by decide
  have hdescent : baseEnd_6406460 < baseStart_6406460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406483 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 5, 2, 2]
def baseStart_6406483 : Nat := 118140960795 + 6406483 * 2 ^ 59
def prefixEnd_6406483 : Nat := 4983230072969 + 3 ^ 40 * 6406483 * 2
def baseEnd_6406483 : Nat := 3289605083858163339499627

theorem tailTrace_6406483 : CollatzResearch.WordTrace tailWord_6406483 prefixEnd_6406483 3289605083858163339499627 := by
  unfold tailWord_6406483
  simp only [CollatzResearch.WordTrace]
  refine ⟨233663631249413706032560103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155775754166275804021706735 233663631249413706032560103)
  ·
    refine ⟨350495446874120559048840155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233663631249413706032560103 350495446874120559048840155)
    ·
      refine ⟨525743170311180838573260233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350495446874120559048840155 525743170311180838573260233)
      ·
        refine ⟨394307377733385628929945175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525743170311180838573260233 394307377733385628929945175)
        ·
          refine ⟨591461066600078443394917763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394307377733385628929945175 591461066600078443394917763)
          ·
            refine ⟨887191599900117665092376645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591461066600078443394917763 887191599900117665092376645)
            ·
              refine ⟨166348424981272062204820621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 887191599900117665092376645 166348424981272062204820621)
              ·
                refine ⟨62380659367977023326807733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166348424981272062204820621 62380659367977023326807733)
                ·
                  refine ⟨5848186815747845936888225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62380659367977023326807733 5848186815747845936888225)
                  ·
                    refine ⟨4386140111810884452666169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5848186815747845936888225 4386140111810884452666169)
                    ·
                      refine ⟨3289605083858163339499627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386140111810884452666169 3289605083858163339499627)
                      ·
                        rfl

theorem cell23_6406483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 2, 2].length) (baseStart_6406483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406483 prefixEnd_6406483 := by exact prefixLift 6406483
  have htrace : WordTrace (prefixWord ++ tailWord_6406483) baseStart_6406483 baseEnd_6406483 := by
    simpa [prefixWord, tailWord_6406483, baseEnd_6406483] using wordTrace_append hprefix tailTrace_6406483
  have hstable : (prefixWord ++ tailWord_6406483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406483).length < 2 ^ (prefixWord ++ tailWord_6406483).sum := by decide
  have hdescent : baseEnd_6406483 < baseStart_6406483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406503 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_6406503 : Nat := 118140960795 + 6406503 * 2 ^ 59
def prefixEnd_6406503 : Nat := 4983230072969 + 3 ^ 40 * 6406503 * 2
def baseEnd_6406503 : Nat := 3289615353471253261249535

theorem tailTrace_6406503 : CollatzResearch.WordTrace tailWord_6406503 prefixEnd_6406503 3289615353471253261249535 := by
  unfold tailWord_6406503
  simp only [CollatzResearch.WordTrace]
  refine ⟨233664360709341249448288163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155776240472894166298858775 233664360709341249448288163)
  ·
    refine ⟨350496541064011874172432245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233664360709341249448288163 350496541064011874172432245)
    ·
      refine ⟨32859050724751113203665523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 350496541064011874172432245 32859050724751113203665523)
      ·
        refine ⟨49288576087126669805498285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32859050724751113203665523 49288576087126669805498285)
        ·
          refine ⟨18483216032672501177061857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49288576087126669805498285 18483216032672501177061857)
          ·
            refine ⟨13862412024504375882796393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18483216032672501177061857 13862412024504375882796393)
            ·
              refine ⟨10396809018378281912097295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13862412024504375882796393 10396809018378281912097295)
              ·
                refine ⟨15595213527567422868145943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396809018378281912097295 15595213527567422868145943)
                ·
                  refine ⟨23392820291351134302218915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15595213527567422868145943 23392820291351134302218915)
                  ·
                    refine ⟨35089230437026701453328373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23392820291351134302218915 35089230437026701453328373)
                    ·
                      refine ⟨3289615353471253261249535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35089230437026701453328373 3289615353471253261249535)
                      ·
                        rfl

theorem cell23_6406503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_6406503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406503 prefixEnd_6406503 := by exact prefixLift 6406503
  have htrace : WordTrace (prefixWord ++ tailWord_6406503) baseStart_6406503 baseEnd_6406503 := by
    simpa [prefixWord, tailWord_6406503, baseEnd_6406503] using wordTrace_append hprefix tailTrace_6406503
  have hstable : (prefixWord ++ tailWord_6406503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406503).length < 2 ^ (prefixWord ++ tailWord_6406503).sum := by decide
  have hdescent : baseEnd_6406503 < baseStart_6406503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406506 : List Nat := [3, 1, 3, 3, 1, 1, 11]
def baseStart_6406506 : Nat := 118140960795 + 6406506 * 2 ^ 59
def prefixEnd_6406506 : Nat := 4983230072969 + 3 ^ 40 * 6406506 * 2
def baseEnd_6406506 : Nat := 40612554245842182092741

theorem tailTrace_6406506 : CollatzResearch.WordTrace tailWord_6406506 prefixEnd_6406506 40612554245842182092741 := by
  unfold tailWord_6406506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58416117532082595240161843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155776313418886920640431581 58416117532082595240161843)
  ·
    refine ⟨87624176298123892860242765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58416117532082595240161843 87624176298123892860242765)
    ·
      refine ⟨32859066111796459822591037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87624176298123892860242765 32859066111796459822591037)
      ·
        refine ⟨12322149791923672433471639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32859066111796459822591037 12322149791923672433471639)
        ·
          refine ⟨18483224687885508650207459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322149791923672433471639 18483224687885508650207459)
          ·
            refine ⟨27724837031828262975311189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18483224687885508650207459 27724837031828262975311189)
            ·
              refine ⟨40612554245842182092741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27724837031828262975311189 40612554245842182092741)
              ·
                rfl

theorem cell23_6406506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 11].length) (baseStart_6406506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406506 prefixEnd_6406506 := by exact prefixLift 6406506
  have htrace : WordTrace (prefixWord ++ tailWord_6406506) baseStart_6406506 baseEnd_6406506 := by
    simpa [prefixWord, tailWord_6406506, baseEnd_6406506] using wordTrace_append hprefix tailTrace_6406506
  have hstable : (prefixWord ++ tailWord_6406506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406506).length < 2 ^ (prefixWord ++ tailWord_6406506).sum := by decide
  have hdescent : baseEnd_6406506 < baseStart_6406506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406517 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6406517 : Nat := 118140960795 + 6406517 * 2 ^ 59
def prefixEnd_6406517 : Nat := 4983230072969 + 3 ^ 40 * 6406517 * 2
def baseEnd_6406517 : Nat := 3289622542200416206474471

theorem tailTrace_6406517 : CollatzResearch.WordTrace tailWord_6406517 prefixEnd_6406517 3289622542200416206474471 := by
  unfold tailWord_6406517
  simp only [CollatzResearch.WordTrace]
  refine ⟨233664871331290529839297805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155776580887527019892865203 233664871331290529839297805)
  ·
    refine ⟨87624326749233948689736677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233664871331290529839297805 87624326749233948689736677)
    ·
      refine ⟨16429561265481365379325627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87624326749233948689736677 16429561265481365379325627)
      ·
        refine ⟨24644341898222048068988441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16429561265481365379325627 24644341898222048068988441)
        ·
          refine ⟨18483256423666536051741331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24644341898222048068988441 18483256423666536051741331)
          ·
            refine ⟨27724884635499804077611997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18483256423666536051741331 27724884635499804077611997)
            ·
              refine ⟨10396831738312426529104499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27724884635499804077611997 10396831738312426529104499)
              ·
                refine ⟨15595247607468639793656749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396831738312426529104499 15595247607468639793656749)
                ·
                  refine ⟨5848217852800739922621281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15595247607468639793656749 5848217852800739922621281)
                  ·
                    refine ⟨4386163389600554941965961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5848217852800739922621281 4386163389600554941965961)
                    ·
                      refine ⟨3289622542200416206474471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386163389600554941965961 3289622542200416206474471)
                      ·
                        rfl

theorem cell23_6406517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6406517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406517 prefixEnd_6406517 := by exact prefixLift 6406517
  have htrace : WordTrace (prefixWord ++ tailWord_6406517) baseStart_6406517 baseEnd_6406517 := by
    simpa [prefixWord, tailWord_6406517, baseEnd_6406517] using wordTrace_append hprefix tailTrace_6406517
  have hstable : (prefixWord ++ tailWord_6406517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406517).length < 2 ^ (prefixWord ++ tailWord_6406517).sum := by decide
  have hdescent : baseEnd_6406517 < baseStart_6406517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406567 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_6406567 : Nat := 118140960795 + 6406567 * 2 ^ 59
def prefixEnd_6406567 : Nat := 4983230072969 + 3 ^ 40 * 6406567 * 2
def baseEnd_6406567 : Nat := 3289648216233141010849241

theorem tailTrace_6406567 : CollatzResearch.WordTrace tailWord_6406567 prefixEnd_6406567 3289648216233141010849241 := by
  unfold tailWord_6406567
  simp only [CollatzResearch.WordTrace]
  refine ⟨233666694981109388378617955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155777796654072925585745303 233666694981109388378617955)
  ·
    refine ⟨350500042471664082567926933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233666694981109388378617955 350500042471664082567926933)
    ·
      refine ⟨16429689490859253870371575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 350500042471664082567926933 16429689490859253870371575)
      ·
        refine ⟨24644534236288880805557363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16429689490859253870371575 24644534236288880805557363)
        ·
          refine ⟨36966801354433321208336045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24644534236288880805557363 36966801354433321208336045)
          ·
            refine ⟨13862550507912495453126017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36966801354433321208336045 13862550507912495453126017)
            ·
              refine ⟨10396912880934371589844513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13862550507912495453126017 10396912880934371589844513)
              ·
                refine ⟨7797684660700778692383385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10396912880934371589844513 7797684660700778692383385)
                ·
                  refine ⟨5848263495525584019287539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7797684660700778692383385 5848263495525584019287539)
                  ·
                    refine ⟨8772395243288376028931309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5848263495525584019287539 8772395243288376028931309)
                    ·
                      refine ⟨3289648216233141010849241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772395243288376028931309 3289648216233141010849241)
                      ·
                        rfl

theorem cell23_6406567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_6406567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406567 prefixEnd_6406567 := by exact prefixLift 6406567
  have htrace : WordTrace (prefixWord ++ tailWord_6406567) baseStart_6406567 baseEnd_6406567 := by
    simpa [prefixWord, tailWord_6406567, baseEnd_6406567] using wordTrace_append hprefix tailTrace_6406567
  have hstable : (prefixWord ++ tailWord_6406567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406567).length < 2 ^ (prefixWord ++ tailWord_6406567).sum := by decide
  have hdescent : baseEnd_6406567 < baseStart_6406567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406568 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6406568 : Nat := 118140960795 + 6406568 * 2 ^ 59
def prefixEnd_6406568 : Nat := 4983230072969 + 3 ^ 40 * 6406568 * 2
def baseEnd_6406568 : Nat := 3289648729713795506936737

theorem tailTrace_6406568 : CollatzResearch.WordTrace tailWord_6406568 prefixEnd_6406568 3289648729713795506936737 := by
  unfold tailWord_6406568
  simp only [CollatzResearch.WordTrace]
  refine ⟨116833365727052882774702179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155777820969403843699602905 116833365727052882774702179)
  ·
    refine ⟨175250048590579324162053269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116833365727052882774702179 175250048590579324162053269)
    ·
      refine ⟨8214846027683405820096247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175250048590579324162053269 8214846027683405820096247)
      ·
        refine ⟨12322269041525108730144371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8214846027683405820096247 12322269041525108730144371)
        ·
          refine ⟨18483403562287663095216557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322269041525108730144371 18483403562287663095216557)
          ·
            refine ⟨6931276335857873660706209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18483403562287663095216557 6931276335857873660706209)
            ·
              refine ⟨5198457251893405245529657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931276335857873660706209 5198457251893405245529657)
              ·
                refine ⟨3898842938920053934147243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5198457251893405245529657 3898842938920053934147243)
                ·
                  refine ⟨5848264408380080901220865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898842938920053934147243 5848264408380080901220865)
                  ·
                    refine ⟨4386198306285060675915649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5848264408380080901220865 4386198306285060675915649)
                    ·
                      refine ⟨3289648729713795506936737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386198306285060675915649 3289648729713795506936737)
                      ·
                        rfl

theorem cell23_6406568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6406568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406568 prefixEnd_6406568 := by exact prefixLift 6406568
  have htrace : WordTrace (prefixWord ++ tailWord_6406568) baseStart_6406568 baseEnd_6406568 := by
    simpa [prefixWord, tailWord_6406568, baseEnd_6406568] using wordTrace_append hprefix tailTrace_6406568
  have hstable : (prefixWord ++ tailWord_6406568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406568).length < 2 ^ (prefixWord ++ tailWord_6406568).sum := by decide
  have hdescent : baseEnd_6406568 < baseStart_6406568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406590 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_6406590 : Nat := 118140960795 + 6406590 * 2 ^ 59
def prefixEnd_6406590 : Nat := 4983230072969 + 3 ^ 40 * 6406590 * 2
def baseEnd_6406590 : Nat := 3289660026288194420861635

theorem tailTrace_6406590 : CollatzResearch.WordTrace tailWord_6406590 prefixEnd_6406590 3289660026288194420861635 := by
  unfold tailWord_6406590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29208441732503257913338153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155778355906684042204470149 29208441732503257913338153)
  ·
    refine ⟨21906331299377443435003615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29208441732503257913338153 21906331299377443435003615)
    ·
      refine ⟨32859496949066165152505423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21906331299377443435003615 32859496949066165152505423)
      ·
        refine ⟨49289245423599247728758135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32859496949066165152505423 49289245423599247728758135)
        ·
          refine ⟨73933868135398871593137203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49289245423599247728758135 73933868135398871593137203)
          ·
            refine ⟨110900802203098307389705805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73933868135398871593137203 110900802203098307389705805)
            ·
              refine ⟨41587800826161865271139677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110900802203098307389705805 41587800826161865271139677)
              ·
                refine ⟨15595425309810699476677379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41587800826161865271139677 15595425309810699476677379)
                ·
                  refine ⟨23393137964716049215016069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15595425309810699476677379 23393137964716049215016069)
                  ·
                    refine ⟨4386213368384259227815513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23393137964716049215016069 4386213368384259227815513)
                    ·
                      refine ⟨3289660026288194420861635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386213368384259227815513 3289660026288194420861635)
                      ·
                        rfl

theorem cell23_6406590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_6406590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406590 prefixEnd_6406590 := by exact prefixLift 6406590
  have htrace : WordTrace (prefixWord ++ tailWord_6406590) baseStart_6406590 baseEnd_6406590 := by
    simpa [prefixWord, tailWord_6406590, baseEnd_6406590] using wordTrace_append hprefix tailTrace_6406590
  have hstable : (prefixWord ++ tailWord_6406590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406590).length < 2 ^ (prefixWord ++ tailWord_6406590).sum := by decide
  have hdescent : baseEnd_6406590 < baseStart_6406590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406606 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6406606 : Nat := 118140960795 + 6406606 * 2 ^ 59
def prefixEnd_6406606 : Nat := 4983230072969 + 3 ^ 40 * 6406606 * 2
def baseEnd_6406606 : Nat := 3289668241978666358261561

theorem tailTrace_6406606 : CollatzResearch.WordTrace tailWord_6406606 prefixEnd_6406606 3289668241978666358261561 := by
  unfold tailWord_6406606
  simp only [CollatzResearch.WordTrace]
  refine ⟨29208514678496012254910959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155778744951978732026191781 29208514678496012254910959)
  ·
    refine ⟨43812772017744018382366439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29208514678496012254910959 43812772017744018382366439)
    ·
      refine ⟨65719158026616027573549659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43812772017744018382366439 65719158026616027573549659)
      ·
        refine ⟨98578737039924041360324489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65719158026616027573549659 98578737039924041360324489)
        ·
          refine ⟨73934052779943031020243367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98578737039924041360324489 73934052779943031020243367)
          ·
            refine ⟨110901079169914546530365051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73934052779943031020243367 110901079169914546530365051)
            ·
              refine ⟨166351618754871819795547577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110901079169914546530365051 166351618754871819795547577)
              ·
                refine ⟨124763714066153864846660683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166351618754871819795547577 124763714066153864846660683)
                ·
                  refine ⟨187145571099230797269991025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124763714066153864846660683 187145571099230797269991025)
                  ·
                    refine ⟨140359178324423097952493269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187145571099230797269991025 140359178324423097952493269)
                    ·
                      refine ⟨3289668241978666358261561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140359178324423097952493269 3289668241978666358261561)
                      ·
                        rfl

theorem cell23_6406606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6406606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406606 prefixEnd_6406606 := by exact prefixLift 6406606
  have htrace : WordTrace (prefixWord ++ tailWord_6406606) baseStart_6406606 baseEnd_6406606 := by
    simpa [prefixWord, tailWord_6406606, baseEnd_6406606] using wordTrace_append hprefix tailTrace_6406606
  have hstable : (prefixWord ++ tailWord_6406606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406606).length < 2 ^ (prefixWord ++ tailWord_6406606).sum := by decide
  have hdescent : baseEnd_6406606 < baseStart_6406606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406623 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_6406623 : Nat := 118140960795 + 6406623 * 2 ^ 59
def prefixEnd_6406623 : Nat := 4983230072969 + 3 ^ 40 * 6406623 * 2
def baseEnd_6406623 : Nat := 3289676971149792791748983

theorem tailTrace_6406623 : CollatzResearch.WordTrace tailWord_6406623 prefixEnd_6406623 3289676971149792791748983 := by
  unfold tailWord_6406623
  simp only [CollatzResearch.WordTrace]
  refine ⟨233668737468906509942656523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155779158312604339961771015 233668737468906509942656523)
  ·
    refine ⟨350503106203359764913984785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233668737468906509942656523 350503106203359764913984785)
    ·
      refine ⟨262877329652519823685488589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350503106203359764913984785 262877329652519823685488589)
      ·
        refine ⟨98578998619694933882058221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262877329652519823685488589 98578998619694933882058221)
        ·
          refine ⟨36967124482385600205771833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98578998619694933882058221 36967124482385600205771833)
          ·
            refine ⟨27725343361789200154328875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36967124482385600205771833 27725343361789200154328875)
            ·
              refine ⟨41588015042683800231493313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27725343361789200154328875 41588015042683800231493313)
              ·
                refine ⟨31191011282012850173619985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41588015042683800231493313 31191011282012850173619985)
                ·
                  refine ⟨23393258461509637630214989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31191011282012850173619985 23393258461509637630214989)
                  ·
                    refine ⟨8772471923066114111330621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23393258461509637630214989 8772471923066114111330621)
                    ·
                      refine ⟨3289676971149792791748983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772471923066114111330621 3289676971149792791748983)
                      ·
                        rfl

theorem cell23_6406623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_6406623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406623 prefixEnd_6406623 := by exact prefixLift 6406623
  have htrace : WordTrace (prefixWord ++ tailWord_6406623) baseStart_6406623 baseEnd_6406623 := by
    simpa [prefixWord, tailWord_6406623, baseEnd_6406623] using wordTrace_append hprefix tailTrace_6406623
  have hstable : (prefixWord ++ tailWord_6406623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406623).length < 2 ^ (prefixWord ++ tailWord_6406623).sum := by decide
  have hdescent : baseEnd_6406623 < baseStart_6406623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406633 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 2, 5, 2]
def baseStart_6406633 : Nat := 118140960795 + 6406633 * 2 ^ 59
def prefixEnd_6406633 : Nat := 4983230072969 + 3 ^ 40 * 6406633 * 2
def baseEnd_6406633 : Nat := 3289682105956337752623937

theorem tailTrace_6406633 : CollatzResearch.WordTrace tailWord_6406633 prefixEnd_6406633 3289682105956337752623937 := by
  unfold tailWord_6406633
  simp only [CollatzResearch.WordTrace]
  refine ⟨233669102198870281650520553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155779401465913521100347035 233669102198870281650520553)
  ·
    refine ⟨175251826649152711237890415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233669102198870281650520553 175251826649152711237890415)
    ·
      refine ⟨262877739973729066856835623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175251826649152711237890415 262877739973729066856835623)
      ·
        refine ⟨394316609960593600285253435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262877739973729066856835623 394316609960593600285253435)
        ·
          refine ⟨591474914940890400427880153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394316609960593600285253435 591474914940890400427880153)
          ·
            refine ⟨443606186205667800320910115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591474914940890400427880153 443606186205667800320910115)
            ·
              refine ⟨665409279308501700481365173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443606186205667800320910115 665409279308501700481365173)
              ·
                refine ⟨62382119935172034420127985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665409279308501700481365173 62382119935172034420127985)
                ·
                  refine ⟨46786589951379025815095989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62382119935172034420127985 46786589951379025815095989)
                  ·
                    refine ⟨4386242807941783670165249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46786589951379025815095989 4386242807941783670165249)
                    ·
                      refine ⟨3289682105956337752623937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386242807941783670165249 3289682105956337752623937)
                      ·
                        rfl

theorem cell23_6406633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 5, 2].length) (baseStart_6406633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406633 prefixEnd_6406633 := by exact prefixLift 6406633
  have htrace : WordTrace (prefixWord ++ tailWord_6406633) baseStart_6406633 baseEnd_6406633 := by
    simpa [prefixWord, tailWord_6406633, baseEnd_6406633] using wordTrace_append hprefix tailTrace_6406633
  have hstable : (prefixWord ++ tailWord_6406633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406633).length < 2 ^ (prefixWord ++ tailWord_6406633).sum := by decide
  have hdescent : baseEnd_6406633 < baseStart_6406633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406636 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_6406636 : Nat := 118140960795 + 6406636 * 2 ^ 59
def prefixEnd_6406636 : Nat := 4983230072969 + 3 ^ 40 * 6406636 * 2
def baseEnd_6406636 : Nat := 3289683646398301240886423

theorem tailTrace_6406636 : CollatzResearch.WordTrace tailWord_6406636 prefixEnd_6406636 3289683646398301240886423 := by
  unfold tailWord_6406636
  simp only [CollatzResearch.WordTrace]
  refine ⟨116834605808929706581439881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155779474411906275441919841 116834605808929706581439881)
  ·
    refine ⟨87625954356697279936079911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116834605808929706581439881 87625954356697279936079911)
    ·
      refine ⟨131438931535045919904119867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87625954356697279936079911 131438931535045919904119867)
      ·
        refine ⟨197158397302568879856179801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131438931535045919904119867 197158397302568879856179801)
        ·
          refine ⟨147868797976926659892134851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197158397302568879856179801 147868797976926659892134851)
          ·
            refine ⟨221803196965389989838202277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147868797976926659892134851 221803196965389989838202277)
            ·
              refine ⟨41588099431010623094662927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221803196965389989838202277 41588099431010623094662927)
              ·
                refine ⟨62382149146515934641994391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41588099431010623094662927 62382149146515934641994391)
                ·
                  refine ⟨93573223719773901962991587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62382149146515934641994391 93573223719773901962991587)
                  ·
                    refine ⟨140359835579660852944487381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93573223719773901962991587 140359835579660852944487381)
                    ·
                      refine ⟨3289683646398301240886423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140359835579660852944487381 3289683646398301240886423)
                      ·
                        rfl

theorem cell23_6406636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_6406636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406636 prefixEnd_6406636 := by exact prefixLift 6406636
  have htrace : WordTrace (prefixWord ++ tailWord_6406636) baseStart_6406636 baseEnd_6406636 := by
    simpa [prefixWord, tailWord_6406636, baseEnd_6406636] using wordTrace_append hprefix tailTrace_6406636
  have hstable : (prefixWord ++ tailWord_6406636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406636).length < 2 ^ (prefixWord ++ tailWord_6406636).sum := by decide
  have hdescent : baseEnd_6406636 < baseStart_6406636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406680 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6406680 : Nat := 118140960795 + 6406680 * 2 ^ 59
def prefixEnd_6406680 : Nat := 4983230072969 + 3 ^ 40 * 6406680 * 2
def baseEnd_6406680 : Nat := 3289706239547099068736221

theorem tailTrace_6406680 : CollatzResearch.WordTrace tailWord_6406680 prefixEnd_6406680 3289706239547099068736221 := by
  unfold tailWord_6406680
  simp only [CollatzResearch.WordTrace]
  refine ⟨116835408214850004338740747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155780544286466672451654329 116835408214850004338740747)
  ·
    refine ⟨175253112322275006508111121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116835408214850004338740747 175253112322275006508111121)
    ·
      refine ⟨131439834241706254881083341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175253112322275006508111121 131439834241706254881083341)
      ·
        refine ⟨49289937840639845580406253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131439834241706254881083341 49289937840639845580406253)
        ·
          refine ⟨18483726690239942092652345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49289937840639845580406253 18483726690239942092652345)
          ·
            refine ⟨13862795017679956569489259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18483726690239942092652345 13862795017679956569489259)
            ·
              refine ⟨20794192526519934854233889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13862795017679956569489259 20794192526519934854233889)
              ·
                refine ⟨15595644394889951140675417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20794192526519934854233889 15595644394889951140675417)
                ·
                  refine ⟨11696733296167463355506563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15595644394889951140675417 11696733296167463355506563)
                  ·
                    refine ⟨17545099944251195033259845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11696733296167463355506563 17545099944251195033259845)
                    ·
                      refine ⟨3289706239547099068736221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17545099944251195033259845 3289706239547099068736221)
                      ·
                        rfl

theorem cell23_6406680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6406680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406680 prefixEnd_6406680 := by exact prefixLift 6406680
  have htrace : WordTrace (prefixWord ++ tailWord_6406680) baseStart_6406680 baseEnd_6406680 := by
    simpa [prefixWord, tailWord_6406680, baseEnd_6406680] using wordTrace_append hprefix tailTrace_6406680
  have hstable : (prefixWord ++ tailWord_6406680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406680).length < 2 ^ (prefixWord ++ tailWord_6406680).sum := by decide
  have hdescent : baseEnd_6406680 < baseStart_6406680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406717 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_6406717 : Nat := 118140960795 + 6406717 * 2 ^ 59
def prefixEnd_6406717 : Nat := 4983230072969 + 3 ^ 40 * 6406717 * 2
def baseEnd_6406717 : Nat := 3289725238331315423973551

theorem tailTrace_6406717 : CollatzResearch.WordTrace tailWord_6406717 prefixEnd_6406717 3289725238331315423973551 := by
  unfold tailWord_6406717
  simp only [CollatzResearch.WordTrace]
  refine ⟨233672165930565963996578405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155781443953710642664385603 233672165930565963996578405)
  ·
    refine ⟨43813531111981118249358451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233672165930565963996578405 43813531111981118249358451)
    ·
      refine ⟨65720296667971677374037677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43813531111981118249358451 65720296667971677374037677)
      ·
        refine ⟨24645111250489379015264129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65720296667971677374037677 24645111250489379015264129)
        ·
          refine ⟨18483833437867034261448097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24645111250489379015264129 18483833437867034261448097)
          ·
            refine ⟨13862875078400275696086073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18483833437867034261448097 13862875078400275696086073)
            ·
              refine ⟨10397156308800206772064555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13862875078400275696086073 10397156308800206772064555)
              ·
                refine ⟨15595734463200310158096833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10397156308800206772064555 15595734463200310158096833)
                ·
                  refine ⟨11696800847400232618572625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15595734463200310158096833 11696800847400232618572625)
                  ·
                    refine ⟨8772600635550174463929469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11696800847400232618572625 8772600635550174463929469)
                    ·
                      refine ⟨3289725238331315423973551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772600635550174463929469 3289725238331315423973551)
                      ·
                        rfl

theorem cell23_6406717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_6406717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406717 prefixEnd_6406717 := by exact prefixLift 6406717
  have htrace : WordTrace (prefixWord ++ tailWord_6406717) baseStart_6406717 baseEnd_6406717 := by
    simpa [prefixWord, tailWord_6406717, baseEnd_6406717] using wordTrace_append hprefix tailTrace_6406717
  have hstable : (prefixWord ++ tailWord_6406717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406717).length < 2 ^ (prefixWord ++ tailWord_6406717).sum := by decide
  have hdescent : baseEnd_6406717 < baseStart_6406717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406774 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6406774 : Nat := 118140960795 + 6406774 * 2 ^ 59
def prefixEnd_6406774 : Nat := 4983230072969 + 3 ^ 40 * 6406774 * 2
def baseEnd_6406774 : Nat := 3289754506728621700960789

theorem tailTrace_6406774 : CollatzResearch.WordTrace tailWord_6406774 prefixEnd_6406774 3289754506728621700960789 := by
  unfold tailWord_6406774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604640305709966420712711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155782829927572975154268917 14604640305709966420712711)
  ·
    refine ⟨21906960458564949631069067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14604640305709966420712711 21906960458564949631069067)
    ·
      refine ⟨32860440687847424446603601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21906960458564949631069067 32860440687847424446603601)
      ·
        refine ⟨24645330515885568334952701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32860440687847424446603601 24645330515885568334952701)
        ·
          refine ⟨9241998943457088125607263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24645330515885568334952701 9241998943457088125607263)
          ·
            refine ⟨13862998415185632188410895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241998943457088125607263 13862998415185632188410895)
            ·
              refine ⟨20794497622778448282616343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13862998415185632188410895 20794497622778448282616343)
              ·
                refine ⟨31191746434167672423924515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20794497622778448282616343 31191746434167672423924515)
                ·
                  refine ⟨46787619651251508635886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31191746434167672423924515 46787619651251508635886773)
                  ·
                    refine ⟨4386339342304828934614385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46787619651251508635886773 4386339342304828934614385)
                    ·
                      refine ⟨3289754506728621700960789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386339342304828934614385 3289754506728621700960789)
                      ·
                        rfl

theorem cell23_6406774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6406774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406774 prefixEnd_6406774 := by exact prefixLift 6406774
  have htrace : WordTrace (prefixWord ++ tailWord_6406774) baseStart_6406774 baseEnd_6406774 := by
    simpa [prefixWord, tailWord_6406774, baseEnd_6406774] using wordTrace_append hprefix tailTrace_6406774
  have hstable : (prefixWord ++ tailWord_6406774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406774).length < 2 ^ (prefixWord ++ tailWord_6406774).sum := by decide
  have hdescent : baseEnd_6406774 < baseStart_6406774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406781 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_6406781 : Nat := 118140960795 + 6406781 * 2 ^ 59
def prefixEnd_6406781 : Nat := 4983230072969 + 3 ^ 40 * 6406781 * 2
def baseEnd_6406781 : Nat := 3289758101093203173573257

theorem tailTrace_6406781 : CollatzResearch.WordTrace tailWord_6406781 prefixEnd_6406781 3289758101093203173573257 := by
  unfold tailWord_6406781
  simp only [CollatzResearch.WordTrace]
  refine ⟨233674500202334102926908197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155783000134889401951272131 233674500202334102926908197)
  ·
    refine ⟨43813968787937644298795287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233674500202334102926908197 43813968787937644298795287)
    ·
      refine ⟨65720953181906466448192931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43813968787937644298795287 65720953181906466448192931)
      ·
        refine ⟨98581429772859699672289397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65720953181906466448192931 98581429772859699672289397)
        ·
          refine ⟨9242009041205596844277131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98581429772859699672289397 9242009041205596844277131)
          ·
            refine ⟨13863013561808395266415697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242009041205596844277131 13863013561808395266415697)
            ·
              refine ⟨10397260171356296449811773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13863013561808395266415697 10397260171356296449811773)
              ·
                refine ⟨3898972564258611168679415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10397260171356296449811773 3898972564258611168679415)
                ·
                  refine ⟨5848458846387916753019123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898972564258611168679415 5848458846387916753019123)
                  ·
                    refine ⟨8772688269581875129528685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5848458846387916753019123 8772688269581875129528685)
                    ·
                      refine ⟨3289758101093203173573257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772688269581875129528685 3289758101093203173573257)
                      ·
                        rfl

theorem cell23_6406781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_6406781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406781 prefixEnd_6406781 := by exact prefixLift 6406781
  have htrace : WordTrace (prefixWord ++ tailWord_6406781) baseStart_6406781 baseEnd_6406781 := by
    simpa [prefixWord, tailWord_6406781, baseEnd_6406781] using wordTrace_append hprefix tailTrace_6406781
  have hstable : (prefixWord ++ tailWord_6406781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406781).length < 2 ^ (prefixWord ++ tailWord_6406781).sum := by decide
  have hdescent : baseEnd_6406781 < baseStart_6406781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406783 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_6406783 : Nat := 118140960795 + 6406783 * 2 ^ 59
def prefixEnd_6406783 : Nat := 4983230072969 + 3 ^ 40 * 6406783 * 2
def baseEnd_6406783 : Nat := 3289759128054512165748247

theorem tailTrace_6406783 : CollatzResearch.WordTrace tailWord_6406783 prefixEnd_6406783 3289759128054512165748247 := by
  unfold tailWord_6406783
  simp only [CollatzResearch.WordTrace]
  refine ⟨233674573148326857268481003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155783048765551238178987335 233674573148326857268481003)
  ·
    refine ⟨350511859722490285902721505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233674573148326857268481003 350511859722490285902721505)
    ·
      refine ⟨262883894791867714427041129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350511859722490285902721505 262883894791867714427041129)
      ·
        refine ⟨197162921093900785820280847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262883894791867714427041129 197162921093900785820280847)
        ·
          refine ⟨295744381640851178730421271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197162921093900785820280847 295744381640851178730421271)
          ·
            refine ⟨443616572461276768095631907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295744381640851178730421271 443616572461276768095631907)
            ·
              refine ⟨665424858691915152143447861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443616572461276768095631907 665424858691915152143447861)
              ·
                refine ⟨62383580502367045513448237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665424858691915152143447861 62383580502367045513448237)
                ·
                  refine ⟨23393842688387642067543089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62383580502367045513448237 23393842688387642067543089)
                  ·
                    refine ⟨17545382016290731550657317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23393842688387642067543089 17545382016290731550657317)
                    ·
                      refine ⟨3289759128054512165748247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17545382016290731550657317 3289759128054512165748247)
                      ·
                        rfl

theorem cell23_6406783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_6406783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406783 prefixEnd_6406783 := by exact prefixLift 6406783
  have htrace : WordTrace (prefixWord ++ tailWord_6406783) baseStart_6406783 baseEnd_6406783 := by
    simpa [prefixWord, tailWord_6406783, baseEnd_6406783] using wordTrace_append hprefix tailTrace_6406783
  have hstable : (prefixWord ++ tailWord_6406783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406783).length < 2 ^ (prefixWord ++ tailWord_6406783).sum := by decide
  have hdescent : baseEnd_6406783 < baseStart_6406783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406787 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 1, 1, 4]
def baseStart_6406787 : Nat := 118140960795 + 6406787 * 2 ^ 59
def prefixEnd_6406787 : Nat := 4983230072969 + 3 ^ 40 * 6406787 * 2
def baseEnd_6406787 : Nat := 3289761181977130150098229

theorem tailTrace_6406787 : CollatzResearch.WordTrace tailWord_6406787 prefixEnd_6406787 3289761181977130150098229 := by
  unfold tailWord_6406787
  simp only [CollatzResearch.WordTrace]
  refine ⟨233674719040312365951626615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155783146026874910634417743 233674719040312365951626615)
  ·
    refine ⟨350512078560468548927439923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233674719040312365951626615 350512078560468548927439923)
    ·
      refine ⟨525768117840702823391159885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350512078560468548927439923 525768117840702823391159885)
      ·
        refine ⟨197163044190263558771684957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525768117840702823391159885 197163044190263558771684957)
        ·
          refine ⟨73936141571348834539381859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197163044190263558771684957 73936141571348834539381859)
          ·
            refine ⟨110904212357023251809072789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73936141571348834539381859 110904212357023251809072789)
            ·
              refine ⟨5198634954235464928550287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110904212357023251809072789 5198634954235464928550287)
              ·
                refine ⟨7797952431353197392825431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198634954235464928550287 7797952431353197392825431)
                ·
                  refine ⟨11696928647029796089238147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7797952431353197392825431 11696928647029796089238147)
                  ·
                    refine ⟨17545392970544694133857221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11696928647029796089238147 17545392970544694133857221)
                    ·
                      refine ⟨3289761181977130150098229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17545392970544694133857221 3289761181977130150098229)
                      ·
                        rfl

theorem cell23_6406787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_6406787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406787 prefixEnd_6406787 := by exact prefixLift 6406787
  have htrace : WordTrace (prefixWord ++ tailWord_6406787) baseStart_6406787 baseEnd_6406787 := by
    simpa [prefixWord, tailWord_6406787, baseEnd_6406787] using wordTrace_append hprefix tailTrace_6406787
  have hstable : (prefixWord ++ tailWord_6406787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406787).length < 2 ^ (prefixWord ++ tailWord_6406787).sum := by decide
  have hdescent : baseEnd_6406787 < baseStart_6406787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406843 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4]
def baseStart_6406843 : Nat := 118140960795 + 6406843 * 2 ^ 59
def prefixEnd_6406843 : Nat := 4983230072969 + 3 ^ 40 * 6406843 * 2
def baseEnd_6406843 : Nat := 3289789936893781930997971

theorem tailTrace_6406843 : CollatzResearch.WordTrace tailWord_6406843 prefixEnd_6406843 3289789936893781930997971 := by
  unfold tailWord_6406843
  simp only [CollatzResearch.WordTrace]
  refine ⟨233676761528109487515665183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155784507685406325010443455 233676761528109487515665183)
  ·
    refine ⟨350515142292164231273497775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233676761528109487515665183 350515142292164231273497775)
    ·
      refine ⟨525772713438246346910246663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350515142292164231273497775 525772713438246346910246663)
      ·
        refine ⟨788659070157369520365369995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525772713438246346910246663 788659070157369520365369995)
        ·
          refine ⟨1182988605236054280548054993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788659070157369520365369995 1182988605236054280548054993)
          ·
            refine ⟨887241453927040710411041245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182988605236054280548054993 887241453927040710411041245)
            ·
              refine ⟨332715545222640266404140467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887241453927040710411041245 332715545222640266404140467)
              ·
                refine ⟨499073317833960399606210701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332715545222640266404140467 499073317833960399606210701)
                ·
                  refine ⟨187152494187735149852329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499073317833960399606210701 187152494187735149852329013)
                  ·
                    refine ⟨17545546330100170298655845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187152494187735149852329013 17545546330100170298655845)
                    ·
                      refine ⟨3289789936893781930997971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17545546330100170298655845 3289789936893781930997971)
                      ·
                        rfl

theorem cell23_6406843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_6406843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406843 prefixEnd_6406843 := by exact prefixLift 6406843
  have htrace : WordTrace (prefixWord ++ tailWord_6406843) baseStart_6406843 baseEnd_6406843 := by
    simpa [prefixWord, tailWord_6406843, baseEnd_6406843] using wordTrace_append hprefix tailTrace_6406843
  have hstable : (prefixWord ++ tailWord_6406843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406843).length < 2 ^ (prefixWord ++ tailWord_6406843).sum := by decide
  have hdescent : baseEnd_6406843 < baseStart_6406843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406871 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 2, 1, 3]
def baseStart_6406871 : Nat := 118140960795 + 6406871 * 2 ^ 59
def prefixEnd_6406871 : Nat := 4983230072969 + 3 ^ 40 * 6406871 * 2
def baseEnd_6406871 : Nat := 3289804314352107821447843

theorem tailTrace_6406871 : CollatzResearch.WordTrace tailWord_6406871 prefixEnd_6406871 3289804314352107821447843 := by
  unfold tailWord_6406871
  simp only [CollatzResearch.WordTrace]
  refine ⟨233677782772008048297684467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155785188514672032198456311 233677782772008048297684467)
  ·
    refine ⟨350516674158012072446526701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233677782772008048297684467 350516674158012072446526701)
    ·
      refine ⟨131443752809254527167447513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350516674158012072446526701 131443752809254527167447513)
      ·
        refine ⟨98582814606940895375585635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131443752809254527167447513 98582814606940895375585635)
        ·
          refine ⟨147874221910411343063378453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98582814606940895375585635 147874221910411343063378453)
          ·
            refine ⟨6931604152050531706095865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147874221910411343063378453 6931604152050531706095865)
            ·
              refine ⟨5198703114037898779571899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931604152050531706095865 5198703114037898779571899)
              ·
                refine ⟨7798054671056848169357849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198703114037898779571899 7798054671056848169357849)
                ·
                  refine ⟨5848541003292636127018387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7798054671056848169357849 5848541003292636127018387)
                  ·
                    refine ⟨8772811504938954190527581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5848541003292636127018387 8772811504938954190527581)
                    ·
                      refine ⟨3289804314352107821447843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772811504938954190527581 3289804314352107821447843)
                      ·
                        rfl

theorem cell23_6406871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_6406871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406871 prefixEnd_6406871 := by exact prefixLift 6406871
  have htrace : WordTrace (prefixWord ++ tailWord_6406871) baseStart_6406871 baseEnd_6406871 := by
    simpa [prefixWord, tailWord_6406871, baseEnd_6406871] using wordTrace_append hprefix tailTrace_6406871
  have hstable : (prefixWord ++ tailWord_6406871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406871).length < 2 ^ (prefixWord ++ tailWord_6406871).sum := by decide
  have hdescent : baseEnd_6406871 < baseStart_6406871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406881 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_6406881 : Nat := 118140960795 + 6406881 * 2 ^ 59
def prefixEnd_6406881 : Nat := 4983230072969 + 3 ^ 40 * 6406881 * 2
def baseEnd_6406881 : Nat := 3289809449158652782322797

theorem tailTrace_6406881 : CollatzResearch.WordTrace tailWord_6406881 prefixEnd_6406881 3289809449158652782322797 := by
  unfold tailWord_6406881
  simp only [CollatzResearch.WordTrace]
  refine ⟨233678147501971820005548497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155785431667981213337032331 233678147501971820005548497)
  ·
    refine ⟨175258610626478865004161373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233678147501971820005548497 175258610626478865004161373)
    ·
      refine ⟨65721978984929574376560515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175258610626478865004161373 65721978984929574376560515)
      ·
        refine ⟨98582968477394361564840773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65721978984929574376560515 98582968477394361564840773)
        ·
          refine ⟨18484306589511442793407645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98582968477394361564840773 18484306589511442793407645)
          ·
            refine ⟨6931614971066791047527867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18484306589511442793407645 6931614971066791047527867)
            ·
              refine ⟨10397422456600186571291801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931614971066791047527867 10397422456600186571291801)
              ·
                refine ⟨7798066842450139928468851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10397422456600186571291801 7798066842450139928468851)
                ·
                  refine ⟨11697100263675209892703277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798066842450139928468851 11697100263675209892703277)
                  ·
                    refine ⟨4386412598878203709763729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11697100263675209892703277 4386412598878203709763729)
                    ·
                      refine ⟨3289809449158652782322797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386412598878203709763729 3289809449158652782322797)
                      ·
                        rfl

theorem cell23_6406881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_6406881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406881 prefixEnd_6406881 := by exact prefixLift 6406881
  have htrace : WordTrace (prefixWord ++ tailWord_6406881) baseStart_6406881 baseEnd_6406881 := by
    simpa [prefixWord, tailWord_6406881, baseEnd_6406881] using wordTrace_append hprefix tailTrace_6406881
  have hstable : (prefixWord ++ tailWord_6406881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406881).length < 2 ^ (prefixWord ++ tailWord_6406881).sum := by decide
  have hdescent : baseEnd_6406881 < baseStart_6406881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406890 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_6406890 : Nat := 118140960795 + 6406890 * 2 ^ 59
def prefixEnd_6406890 : Nat := 4983230072969 + 3 ^ 40 * 6406890 * 2
def baseEnd_6406890 : Nat := 3289814070484543247110255

theorem tailTrace_6406890 : CollatzResearch.WordTrace tailWord_6406890 prefixEnd_6406890 3289814070484543247110255 := by
  unfold tailWord_6406890
  simp only [CollatzResearch.WordTrace]
  refine ⟨58419618939734803635656531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155785650505959476361750749 58419618939734803635656531)
  ·
    refine ⟨87629428409602205453484797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58419618939734803635656531 87629428409602205453484797)
    ·
      refine ⟨32861035653600827045056799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87629428409602205453484797 32861035653600827045056799)
      ·
        refine ⟨49291553480401240567585199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32861035653600827045056799 49291553480401240567585199)
        ·
          refine ⟨73937330220601860851377799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49291553480401240567585199 73937330220601860851377799)
          ·
            refine ⟨110905995330902791277066699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73937330220601860851377799 110905995330902791277066699)
            ·
              refine ⟨166358992996354186915600049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110905995330902791277066699 166358992996354186915600049)
              ·
                refine ⟨124769244747265640186700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166358992996354186915600049 124769244747265640186700037)
                ·
                  refine ⟨23394233390112307535006257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124769244747265640186700037 23394233390112307535006257)
                  ·
                    refine ⟨17545675042584230651254693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23394233390112307535006257 17545675042584230651254693)
                    ·
                      refine ⟨3289814070484543247110255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17545675042584230651254693 3289814070484543247110255)
                      ·
                        rfl

theorem cell23_6406890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_6406890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406890 prefixEnd_6406890 := by exact prefixLift 6406890
  have htrace : WordTrace (prefixWord ++ tailWord_6406890) baseStart_6406890 baseEnd_6406890 := by
    simpa [prefixWord, tailWord_6406890, baseEnd_6406890] using wordTrace_append hprefix tailTrace_6406890
  have hstable : (prefixWord ++ tailWord_6406890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406890).length < 2 ^ (prefixWord ++ tailWord_6406890).sum := by decide
  have hdescent : baseEnd_6406890 < baseStart_6406890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406894 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_6406894 : Nat := 118140960795 + 6406894 * 2 ^ 59
def prefixEnd_6406894 : Nat := 4983230072969 + 3 ^ 40 * 6406894 * 2
def baseEnd_6406894 : Nat := 3289816124407161231460237

theorem tailTrace_6406894 : CollatzResearch.WordTrace tailWord_6406894 prefixEnd_6406894 3289816124407161231460237 := by
  unfold tailWord_6406894
  simp only [CollatzResearch.WordTrace]
  refine ⟨29209827706365590403221467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155785747767283148817181157 29209827706365590403221467)
  ·
    refine ⟨43814741559548385604832201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29209827706365590403221467 43814741559548385604832201)
    ·
      refine ⟨32861056169661289203624151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43814741559548385604832201 32861056169661289203624151)
      ·
        refine ⟨49291584254491933805436227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32861056169661289203624151 49291584254491933805436227)
        ·
          refine ⟨73937376381737900708154341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49291584254491933805436227 73937376381737900708154341)
          ·
            refine ⟨13863258071575856382778939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73937376381737900708154341 13863258071575856382778939)
            ·
              refine ⟨20794887107363784574168409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13863258071575856382778939 20794887107363784574168409)
              ·
                refine ⟨15596165330522838430626307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20794887107363784574168409 15596165330522838430626307)
                ·
                  refine ⟨23394247995784257645939461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15596165330522838430626307 23394247995784257645939461)
                  ·
                    refine ⟨4386421499209548308613649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23394247995784257645939461 4386421499209548308613649)
                    ·
                      refine ⟨3289816124407161231460237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386421499209548308613649 3289816124407161231460237)
                      ·
                        rfl

theorem cell23_6406894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_6406894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406894 prefixEnd_6406894 := by exact prefixLift 6406894
  have htrace : WordTrace (prefixWord ++ tailWord_6406894) baseStart_6406894 baseEnd_6406894 := by
    simpa [prefixWord, tailWord_6406894, baseEnd_6406894] using wordTrace_append hprefix tailTrace_6406894
  have hstable : (prefixWord ++ tailWord_6406894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406894).length < 2 ^ (prefixWord ++ tailWord_6406894).sum := by decide
  have hdescent : baseEnd_6406894 < baseStart_6406894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6406967 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 4, 4, 2]
def baseStart_6406967 : Nat := 118140960795 + 6406967 * 2 ^ 59
def prefixEnd_6406967 : Nat := 4983230072969 + 3 ^ 40 * 6406967 * 2
def baseEnd_6406967 : Nat := 3289853608494939445847401

theorem tailTrace_6406967 : CollatzResearch.WordTrace tailWord_6406967 prefixEnd_6406967 3289853608494939445847401 := by
  unfold tailWord_6406967
  simp only [CollatzResearch.WordTrace]
  refine ⟨233681284179660256693179155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155787522786440171128786103 233681284179660256693179155)
  ·
    refine ⟨350521926269490385039768733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233681284179660256693179155 350521926269490385039768733)
    ·
      refine ⟨131445722351058894389913275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350521926269490385039768733 131445722351058894389913275)
      ·
        refine ⟨197168583526588341584869913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131445722351058894389913275 197168583526588341584869913)
        ·
          refine ⟨147876437644941256188652435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197168583526588341584869913 147876437644941256188652435)
          ·
            refine ⟨221814656467411884282978653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147876437644941256188652435 221814656467411884282978653)
            ·
              refine ⟨83180496175279456606116995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221814656467411884282978653 83180496175279456606116995)
              ·
                refine ⟨124770744262919184909175493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83180496175279456606116995 124770744262919184909175493)
                ·
                  refine ⟨23394514549297347170470405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124770744262919184909175493 23394514549297347170470405)
                  ·
                    refine ⟨4386471477993252594463201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23394514549297347170470405 4386471477993252594463201)
                    ·
                      refine ⟨3289853608494939445847401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386471477993252594463201 3289853608494939445847401)
                      ·
                        rfl

theorem cell23_6406967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_6406967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6406967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6406967 prefixEnd_6406967 := by exact prefixLift 6406967
  have htrace : WordTrace (prefixWord ++ tailWord_6406967) baseStart_6406967 baseEnd_6406967 := by
    simpa [prefixWord, tailWord_6406967, baseEnd_6406967] using wordTrace_append hprefix tailTrace_6406967
  have hstable : (prefixWord ++ tailWord_6406967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6406967).length < 2 ^ (prefixWord ++ tailWord_6406967).sum := by decide
  have hdescent : baseEnd_6406967 < baseStart_6406967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6406967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407004 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6407004 : Nat := 118140960795 + 6407004 * 2 ^ 59
def prefixEnd_6407004 : Nat := 4983230072969 + 3 ^ 40 * 6407004 * 2
def baseEnd_6407004 : Nat := 3289872607279155801084731

theorem tailTrace_6407004 : CollatzResearch.WordTrace tailWord_6407004 prefixEnd_6407004 3289872607279155801084731 := by
  unfold tailWord_6407004
  simp only [CollatzResearch.WordTrace]
  refine ⟨116841316840263106006138033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155788422453684141341517377 116841316840263106006138033)
  ·
    refine ⟨87630987630197329504603525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116841316840263106006138033 87630987630197329504603525)
    ·
      refine ⟨16430810180661999282113161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87630987630197329504603525 16430810180661999282113161)
      ·
        refine ⟨12323107635496499461584871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16430810180661999282113161 12323107635496499461584871)
        ·
          refine ⟨18484661453244749192377307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12323107635496499461584871 18484661453244749192377307)
          ·
            refine ⟨27726992179867123788565961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18484661453244749192377307 27726992179867123788565961)
            ·
              refine ⟨20795244134900342841424471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27726992179867123788565961 20795244134900342841424471)
              ·
                refine ⟨31192866202350514262136707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20795244134900342841424471 31192866202350514262136707)
                ·
                  refine ⟨46789299303525771393205061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31192866202350514262136707 46789299303525771393205061)
                  ·
                    refine ⟨8772993619411082136225949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46789299303525771393205061 8772993619411082136225949)
                    ·
                      refine ⟨3289872607279155801084731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8772993619411082136225949 3289872607279155801084731)
                      ·
                        rfl

theorem cell23_6407004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6407004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407004 prefixEnd_6407004 := by exact prefixLift 6407004
  have htrace : WordTrace (prefixWord ++ tailWord_6407004) baseStart_6407004 baseEnd_6407004 := by
    simpa [prefixWord, tailWord_6407004, baseEnd_6407004] using wordTrace_append hprefix tailTrace_6407004
  have hstable : (prefixWord ++ tailWord_6407004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407004).length < 2 ^ (prefixWord ++ tailWord_6407004).sum := by decide
  have hdescent : baseEnd_6407004 < baseStart_6407004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407011 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 1, 4]
def baseStart_6407011 : Nat := 118140960795 + 6407011 * 2 ^ 59
def prefixEnd_6407011 : Nat := 4983230072969 + 3 ^ 40 * 6407011 * 2
def baseEnd_6407011 : Nat := 1096625400547912424565733

theorem tailTrace_6407011 : CollatzResearch.WordTrace tailWord_6407011 prefixEnd_6407011 1096625400547912424565733 := by
  unfold tailWord_6407011
  simp only [CollatzResearch.WordTrace]
  refine ⟨233682888991500852207780887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155788592661000568138520591 233682888991500852207780887)
  ·
    refine ⟨350524333487251278311671331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233682888991500852207780887 350524333487251278311671331)
    ·
      refine ⟨525786500230876917467506997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350524333487251278311671331 525786500230876917467506997)
      ·
        refine ⟨49292484396644711012578781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 525786500230876917467506997 49292484396644711012578781)
        ·
          refine ⟨18484681648741766629717043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49292484396644711012578781 18484681648741766629717043)
          ·
            refine ⟨27727022473112649944575565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18484681648741766629717043 27727022473112649944575565)
            ·
              refine ⟨10397633427417243729215837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27727022473112649944575565 10397633427417243729215837)
              ·
                refine ⟨3899112535281466398455939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10397633427417243729215837 3899112535281466398455939)
                ·
                  refine ⟨5848668802922199597683909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899112535281466398455939 5848668802922199597683909)
                  ·
                    refine ⟨1096625400547912424565733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848668802922199597683909 1096625400547912424565733)
                    ·
                      rfl

theorem cell23_6407011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 4].length) (baseStart_6407011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407011 prefixEnd_6407011 := by exact prefixLift 6407011
  have htrace : WordTrace (prefixWord ++ tailWord_6407011) baseStart_6407011 baseEnd_6407011 := by
    simpa [prefixWord, tailWord_6407011, baseEnd_6407011] using wordTrace_append hprefix tailTrace_6407011
  have hstable : (prefixWord ++ tailWord_6407011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407011).length < 2 ^ (prefixWord ++ tailWord_6407011).sum := by decide
  have hdescent : baseEnd_6407011 < baseStart_6407011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407044 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_6407044 : Nat := 118140960795 + 6407044 * 2 ^ 59
def prefixEnd_6407044 : Nat := 4983230072969 + 3 ^ 40 * 6407044 * 2
def baseEnd_6407044 : Nat := 3289893146505335644584547

theorem tailTrace_6407044 : CollatzResearch.WordTrace tailWord_6407044 prefixEnd_6407044 3289893146505335644584547 := by
  unfold tailWord_6407044
  simp only [CollatzResearch.WordTrace]
  refine ⟨116842046300190649421866093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155789395066920865895821457 116842046300190649421866093)
  ·
    refine ⟨43815767362571493533199785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116842046300190649421866093 43815767362571493533199785)
    ·
      refine ⟨32861825521928620149899839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43815767362571493533199785 32861825521928620149899839)
      ·
        refine ⟨49292738282892930224849759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32861825521928620149899839 49292738282892930224849759)
        ·
          refine ⟨73939107424339395337274639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49292738282892930224849759 73939107424339395337274639)
          ·
            refine ⟨110908661136509093005911959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73939107424339395337274639 110908661136509093005911959)
            ·
              refine ⟨166362991704763639508867939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110908661136509093005911959 166362991704763639508867939)
              ·
                refine ⟨249544487557145459263301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166362991704763639508867939 249544487557145459263301909)
                ·
                  refine ⟨11697397854241193402967277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249544487557145459263301909 11697397854241193402967277)
                  ·
                    refine ⟨4386524195340447526112729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11697397854241193402967277 4386524195340447526112729)
                    ·
                      refine ⟨3289893146505335644584547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386524195340447526112729 3289893146505335644584547)
                      ·
                        rfl

theorem cell23_6407044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_6407044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407044 prefixEnd_6407044 := by exact prefixLift 6407044
  have htrace : WordTrace (prefixWord ++ tailWord_6407044) baseStart_6407044 baseEnd_6407044 := by
    simpa [prefixWord, tailWord_6407044, baseEnd_6407044] using wordTrace_append hprefix tailTrace_6407044
  have hstable : (prefixWord ++ tailWord_6407044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407044).length < 2 ^ (prefixWord ++ tailWord_6407044).sum := by decide
  have hdescent : baseEnd_6407044 < baseStart_6407044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407061 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_6407061 : Nat := 118140960795 + 6407061 * 2 ^ 59
def prefixEnd_6407061 : Nat := 4983230072969 + 3 ^ 40 * 6407061 * 2
def baseEnd_6407061 : Nat := 3289901875676462078071969

theorem tailTrace_6407061 : CollatzResearch.WordTrace tailWord_6407061 prefixEnd_6407061 3289901875676462078071969 := by
  unfold tailWord_6407061
  simp only [CollatzResearch.WordTrace]
  refine ⟨233684712641319710747101037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155789808427546473831400691 233684712641319710747101037)
  ·
    refine ⟨87631767240494891530162889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233684712641319710747101037 87631767240494891530162889)
    ·
      refine ⟨65723825430371168647622167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87631767240494891530162889 65723825430371168647622167)
      ·
        refine ⟨98585738145556752971433251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65723825430371168647622167 98585738145556752971433251)
        ·
          refine ⟨147878607218335129457149877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98585738145556752971433251 147878607218335129457149877)
          ·
            refine ⟨13863619426718918386607801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147878607218335129457149877 13863619426718918386607801)
            ·
              refine ⟨10397714570039188789955851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13863619426718918386607801 10397714570039188789955851)
              ·
                refine ⟨15596571855058783184933777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10397714570039188789955851 15596571855058783184933777)
                ·
                  refine ⟨11697428891294087388700333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15596571855058783184933777 11697428891294087388700333)
                  ·
                    refine ⟨4386535834235282770762625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11697428891294087388700333 4386535834235282770762625)
                    ·
                      refine ⟨3289901875676462078071969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386535834235282770762625 3289901875676462078071969)
                      ·
                        rfl

theorem cell23_6407061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_6407061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407061 prefixEnd_6407061 := by exact prefixLift 6407061
  have htrace : WordTrace (prefixWord ++ tailWord_6407061) baseStart_6407061 baseEnd_6407061 := by
    simpa [prefixWord, tailWord_6407061, baseEnd_6407061] using wordTrace_append hprefix tailTrace_6407061
  have hstable : (prefixWord ++ tailWord_6407061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407061).length < 2 ^ (prefixWord ++ tailWord_6407061).sum := by decide
  have hdescent : baseEnd_6407061 < baseStart_6407061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407071 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 1, 5]
def baseStart_6407071 : Nat := 118140960795 + 6407071 * 2 ^ 59
def prefixEnd_6407071 : Nat := 4983230072969 + 3 ^ 40 * 6407071 * 2
def baseEnd_6407071 : Nat := 1096635670161002346315641

theorem tailTrace_6407071 : CollatzResearch.WordTrace tailWord_6407071 prefixEnd_6407071 1096635670161002346315641 := by
  unfold tailWord_6407071
  simp only [CollatzResearch.WordTrace]
  refine ⟨233685077371283482454965067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155790051580855654969976711 233685077371283482454965067)
  ·
    refine ⟨350527616056925223682447601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233685077371283482454965067 350527616056925223682447601)
    ·
      refine ⟨262895712042693917761835701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350527616056925223682447601 262895712042693917761835701)
      ·
        refine ⟨24646473004002554790172097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262895712042693917761835701 24646473004002554790172097)
        ·
          refine ⟨18484854753001916092629073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24646473004002554790172097 18484854753001916092629073)
          ·
            refine ⟨13863641064751437069471805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18484854753001916092629073 13863641064751437069471805)
            ·
              refine ⟨5198865399281788901051927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13863641064751437069471805 5198865399281788901051927)
              ·
                refine ⟨7798298098922683351577891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198865399281788901051927 7798298098922683351577891)
                ·
                  refine ⟨11697447148384025027366837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798298098922683351577891 11697447148384025027366837)
                  ·
                    refine ⟨1096635670161002346315641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11697447148384025027366837 1096635670161002346315641)
                    ·
                      rfl

theorem cell23_6407071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 5].length) (baseStart_6407071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407071 prefixEnd_6407071 := by exact prefixLift 6407071
  have htrace : WordTrace (prefixWord ++ tailWord_6407071) baseStart_6407071 baseEnd_6407071 := by
    simpa [prefixWord, tailWord_6407071, baseEnd_6407071] using wordTrace_append hprefix tailTrace_6407071
  have hstable : (prefixWord ++ tailWord_6407071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407071).length < 2 ^ (prefixWord ++ tailWord_6407071).sum := by decide
  have hdescent : baseEnd_6407071 < baseStart_6407071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407097 : List Nat := [1, 2, 1, 4, 2, 2, 3, 8]
def baseStart_6407097 : Nat := 118140960795 + 6407097 * 2 ^ 59
def prefixEnd_6407097 : Nat := 4983230072969 + 3 ^ 40 * 6407097 * 2
def baseEnd_6407097 : Nat := 121848902258519405082289

theorem tailTrace_6407097 : CollatzResearch.WordTrace tailWord_6407097 prefixEnd_6407097 121848902258519405082289 := by
  unfold tailWord_6407097
  simp only [CollatzResearch.WordTrace]
  refine ⟨233686025669189288895411545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155790683779459525930274363 233686025669189288895411545)
  ·
    refine ⟨175264519251891966671558659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233686025669189288895411545 175264519251891966671558659)
    ·
      refine ⟨262896778877837950007337989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175264519251891966671558659 262896778877837950007337989)
      ·
        refine ⟨49293146039594615626375873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262896778877837950007337989 49293146039594615626375873)
        ·
          refine ⟨36969859529695961719781905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49293146039594615626375873 36969859529695961719781905)
          ·
            refine ⟨27727394647271971289836429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36969859529695961719781905 27727394647271971289836429)
            ·
              refine ⟨10397772992726989233688661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27727394647271971289836429 10397772992726989233688661)
              ·
                refine ⟨121848902258519405082289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10397772992726989233688661 121848902258519405082289)
                ·
                  rfl

theorem cell23_6407097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 8].length) (baseStart_6407097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407097 prefixEnd_6407097 := by exact prefixLift 6407097
  have htrace : WordTrace (prefixWord ++ tailWord_6407097) baseStart_6407097 baseEnd_6407097 := by
    simpa [prefixWord, tailWord_6407097, baseEnd_6407097] using wordTrace_append hprefix tailTrace_6407097
  have hstable : (prefixWord ++ tailWord_6407097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407097).length < 2 ^ (prefixWord ++ tailWord_6407097).sum := by decide
  have hdescent : baseEnd_6407097 < baseStart_6407097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407104 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_6407104 : Nat := 118140960795 + 6407104 * 2 ^ 59
def prefixEnd_6407104 : Nat := 4983230072969 + 3 ^ 40 * 6407104 * 2
def baseEnd_6407104 : Nat := 3289923955344605409834271

theorem tailTrace_6407104 : CollatzResearch.WordTrace tailWord_6407104 prefixEnd_6407104 3289923955344605409834271 := by
  unfold tailWord_6407104
  simp only [CollatzResearch.WordTrace]
  refine ⟨116843140490081964545458183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155790853986775952727277577 116843140490081964545458183)
  ·
    refine ⟨175264710735122946818187275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116843140490081964545458183 175264710735122946818187275)
    ·
      refine ⟨262897066102684420227280913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175264710735122946818187275 262897066102684420227280913)
      ·
        refine ⟨197172799577013315170460685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262897066102684420227280913 197172799577013315170460685)
        ·
          refine ⟨73939799841379993188922757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197172799577013315170460685 73939799841379993188922757)
          ·
            refine ⟨13863712470258748722923017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73939799841379993188922757 13863712470258748722923017)
            ·
              refine ⟨10397784352694061542192263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13863712470258748722923017 10397784352694061542192263)
              ·
                refine ⟨15596676529041092313288395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10397784352694061542192263 15596676529041092313288395)
                ·
                  refine ⟨23395014793561638469932593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15596676529041092313288395 23395014793561638469932593)
                  ·
                    refine ⟨17546261095171228852449445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23395014793561638469932593 17546261095171228852449445)
                    ·
                      refine ⟨3289923955344605409834271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17546261095171228852449445 3289923955344605409834271)
                      ·
                        rfl

theorem cell23_6407104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_6407104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407104 prefixEnd_6407104 := by exact prefixLift 6407104
  have htrace : WordTrace (prefixWord ++ tailWord_6407104) baseStart_6407104 baseEnd_6407104 := by
    simpa [prefixWord, tailWord_6407104, baseEnd_6407104] using wordTrace_append hprefix tailTrace_6407104
  have hstable : (prefixWord ++ tailWord_6407104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407104).length < 2 ^ (prefixWord ++ tailWord_6407104).sum := by decide
  have hdescent : baseEnd_6407104 < baseStart_6407104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407107 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 3]
def baseStart_6407107 : Nat := 118140960795 + 6407107 * 2 ^ 59
def prefixEnd_6407107 : Nat := 4983230072969 + 3 ^ 40 * 6407107 * 2
def baseEnd_6407107 : Nat := 3289925495786568898096757

theorem tailTrace_6407107 : CollatzResearch.WordTrace tailWord_6407107 prefixEnd_6407107 3289925495786568898096757 := by
  unfold tailWord_6407107
  simp only [CollatzResearch.WordTrace]
  refine ⟨233686390399153060603275575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155790926932768707068850383 233686390399153060603275575)
  ·
    refine ⟨350529585598729590904913363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233686390399153060603275575 350529585598729590904913363)
    ·
      refine ⟨525794378398094386357370045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350529585598729590904913363 525794378398094386357370045)
      ·
        refine ⟨197172891899285394884013767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525794378398094386357370045 197172891899285394884013767)
        ·
          refine ⟨295759337848928092326020651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197172891899285394884013767 295759337848928092326020651)
          ·
            refine ⟨443639006773392138489030977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295759337848928092326020651 443639006773392138489030977)
            ·
              refine ⟨332729255080044103866773233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443639006773392138489030977 332729255080044103866773233)
              ·
                refine ⟨249546941310033077900079925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332729255080044103866773233 249546941310033077900079925)
                ·
                  refine ⟨23395025747815601053132493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249546941310033077900079925 23395025747815601053132493)
                  ·
                    refine ⟨8773134655430850394924685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23395025747815601053132493 8773134655430850394924685)
                    ·
                      refine ⟨3289925495786568898096757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8773134655430850394924685 3289925495786568898096757)
                      ·
                        rfl

theorem cell23_6407107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_6407107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407107 prefixEnd_6407107 := by exact prefixLift 6407107
  have htrace : WordTrace (prefixWord ++ tailWord_6407107) baseStart_6407107 baseEnd_6407107 := by
    simpa [prefixWord, tailWord_6407107, baseEnd_6407107] using wordTrace_append hprefix tailTrace_6407107
  have hstable : (prefixWord ++ tailWord_6407107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407107).length < 2 ^ (prefixWord ++ tailWord_6407107).sum := by decide
  have hdescent : baseEnd_6407107 < baseStart_6407107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407125 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6407125 : Nat := 118140960795 + 6407125 * 2 ^ 59
def prefixEnd_6407125 : Nat := 4983230072969 + 3 ^ 40 * 6407125 * 2
def baseEnd_6407125 : Nat := 3289934738438349827671675

theorem tailTrace_6407125 : CollatzResearch.WordTrace tailWord_6407125 prefixEnd_6407125 3289934738438349827671675 := by
  unfold tailWord_6407125
  simp only [CollatzResearch.WordTrace]
  refine ⟨233687046913087849677430829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155791364608725233118287219 233687046913087849677430829)
  ·
    refine ⟨87632642592407943629036561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233687046913087849677430829 87632642592407943629036561)
    ·
      refine ⟨65724481944305957721777421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87632642592407943629036561 65724481944305957721777421)
      ·
        refine ⟨24646680729114734145666533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65724481944305957721777421 24646680729114734145666533)
        ·
          refine ⟨4621252636709012652312475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24646680729114734145666533 4621252636709012652312475)
          ·
            refine ⟨6931878955063518978468713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621252636709012652312475 6931878955063518978468713)
            ·
              refine ⟨5198909216297639233851535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931878955063518978468713 5198909216297639233851535)
              ·
                refine ⟨7798363824446458850777303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198909216297639233851535 7798363824446458850777303)
                ·
                  refine ⟨11697545736669688276165955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798363824446458850777303 11697545736669688276165955)
                  ·
                    refine ⟨17546318605004532414248933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11697545736669688276165955 17546318605004532414248933)
                    ·
                      refine ⟨3289934738438349827671675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17546318605004532414248933 3289934738438349827671675)
                      ·
                        rfl

theorem cell23_6407125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6407125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407125 prefixEnd_6407125 := by exact prefixLift 6407125
  have htrace : WordTrace (prefixWord ++ tailWord_6407125) baseStart_6407125 baseEnd_6407125 := by
    simpa [prefixWord, tailWord_6407125, baseEnd_6407125] using wordTrace_append hprefix tailTrace_6407125
  have hstable : (prefixWord ++ tailWord_6407125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407125).length < 2 ^ (prefixWord ++ tailWord_6407125).sum := by decide
  have hdescent : baseEnd_6407125 < baseStart_6407125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407128 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 1, 2, 3]
def baseStart_6407128 : Nat := 118140960795 + 6407128 * 2 ^ 59
def prefixEnd_6407128 : Nat := 4983230072969 + 3 ^ 40 * 6407128 * 2
def baseEnd_6407128 : Nat := 3289936278880313315934161

theorem tailTrace_6407128 : CollatzResearch.WordTrace tailWord_6407128 prefixEnd_6407128 3289936278880313315934161 := by
  unfold tailWord_6407128
  simp only [CollatzResearch.WordTrace]
  refine ⟨116843578166038490594895019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155791437554717987459860025 116843578166038490594895019)
  ·
    refine ⟨175265367249057735892342529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116843578166038490594895019 175265367249057735892342529)
    ·
      refine ⟨131449025436793301919256897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175265367249057735892342529 131449025436793301919256897)
      ·
        refine ⟨98586769077594976439442673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131449025436793301919256897 98586769077594976439442673)
        ·
          refine ⟨73940076808196232329582005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98586769077594976439442673 73940076808196232329582005)
          ·
            refine ⟨6931882200768396780898313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73940076808196232329582005 6931882200768396780898313)
            ·
              refine ⟨5198911650576297585673735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931882200768396780898313 5198911650576297585673735)
              ·
                refine ⟨7798367475864446378510603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198911650576297585673735 7798367475864446378510603)
                ·
                  refine ⟨11697551213796669567765905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798367475864446378510603 11697551213796669567765905)
                  ·
                    refine ⟨8773163410347502175824429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11697551213796669567765905 8773163410347502175824429)
                    ·
                      refine ⟨3289936278880313315934161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8773163410347502175824429 3289936278880313315934161)
                      ·
                        rfl

theorem cell23_6407128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_6407128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407128 prefixEnd_6407128 := by exact prefixLift 6407128
  have htrace : WordTrace (prefixWord ++ tailWord_6407128) baseStart_6407128 baseEnd_6407128 := by
    simpa [prefixWord, tailWord_6407128, baseEnd_6407128] using wordTrace_append hprefix tailTrace_6407128
  have hstable : (prefixWord ++ tailWord_6407128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407128).length < 2 ^ (prefixWord ++ tailWord_6407128).sum := by decide
  have hdescent : baseEnd_6407128 < baseStart_6407128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407158 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6407158 : Nat := 118140960795 + 6407158 * 2 ^ 59
def prefixEnd_6407158 : Nat := 4983230072969 + 3 ^ 40 * 6407158 * 2
def baseEnd_6407158 : Nat := 3289951683299948198559023

theorem tailTrace_6407158 : CollatzResearch.WordTrace tailWord_6407158 prefixEnd_6407158 3289951683299948198559023 := by
  unfold tailWord_6407158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605515657623018519586383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155792167014645530875588085 14605515657623018519586383)
  ·
    refine ⟨21908273486434527779379575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14605515657623018519586383 21908273486434527779379575)
    ·
      refine ⟨32862410229651791669069363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21908273486434527779379575 32862410229651791669069363)
      ·
        refine ⟨49293615344477687503604045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32862410229651791669069363 49293615344477687503604045)
        ·
          refine ⟨18485105754179132813851517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49293615344477687503604045 18485105754179132813851517)
          ·
            refine ⟨6931914657817174805194319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18485105754179132813851517 6931914657817174805194319)
            ·
              refine ⟨10397871986725762207791479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931914657817174805194319 10397871986725762207791479)
              ·
                refine ⟨15596807980088643311687219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10397871986725762207791479 15596807980088643311687219)
                ·
                  refine ⟨23395211970132964967530829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15596807980088643311687219 23395211970132964967530829)
                  ·
                    refine ⟨8773204488799861862824061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23395211970132964967530829 8773204488799861862824061)
                    ·
                      refine ⟨3289951683299948198559023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8773204488799861862824061 3289951683299948198559023)
                      ·
                        rfl

theorem cell23_6407158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6407158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407158 prefixEnd_6407158 := by exact prefixLift 6407158
  have htrace : WordTrace (prefixWord ++ tailWord_6407158) baseStart_6407158 baseEnd_6407158 := by
    simpa [prefixWord, tailWord_6407158, baseEnd_6407158] using wordTrace_append hprefix tailTrace_6407158
  have hstable : (prefixWord ++ tailWord_6407158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407158).length < 2 ^ (prefixWord ++ tailWord_6407158).sum := by decide
  have hdescent : baseEnd_6407158 < baseStart_6407158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407177 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_6407177 : Nat := 118140960795 + 6407177 * 2 ^ 59
def prefixEnd_6407177 : Nat := 4983230072969 + 3 ^ 40 * 6407177 * 2
def baseEnd_6407177 : Nat := 3289961439432383624221435

theorem tailTrace_6407177 : CollatzResearch.WordTrace tailWord_6407177 prefixEnd_6407177 3289961439432383624221435 := by
  unfold tailWord_6407177
  simp only [CollatzResearch.WordTrace]
  refine ⟨233688943508899462558323785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155792629005932975038882523 233688943508899462558323785)
  ·
    refine ⟨175266707631674596918742839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233688943508899462558323785 175266707631674596918742839)
    ·
      refine ⟨262900061447511895378114259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175266707631674596918742839 262900061447511895378114259)
      ·
        refine ⟨394350092171267843067171389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262900061447511895378114259 394350092171267843067171389)
        ·
          refine ⟨147881284564225441150189271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394350092171267843067171389 147881284564225441150189271)
          ·
            refine ⟨221821926846338161725283907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147881284564225441150189271 221821926846338161725283907)
            ·
              refine ⟨332732890269507242587925861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221821926846338161725283907 332732890269507242587925861)
              ·
                refine ⟨62387416925532607985236099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332732890269507242587925861 62387416925532607985236099)
                ·
                  refine ⟨93581125388298911977854149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62387416925532607985236099 93581125388298911977854149)
                  ·
                    refine ⟨17546461010306045995847653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93581125388298911977854149 17546461010306045995847653)
                    ·
                      refine ⟨3289961439432383624221435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17546461010306045995847653 3289961439432383624221435)
                      ·
                        rfl

theorem cell23_6407177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_6407177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407177 prefixEnd_6407177 := by exact prefixLift 6407177
  have htrace : WordTrace (prefixWord ++ tailWord_6407177) baseStart_6407177 baseEnd_6407177 := by
    simpa [prefixWord, tailWord_6407177, baseEnd_6407177] using wordTrace_append hprefix tailTrace_6407177
  have hstable : (prefixWord ++ tailWord_6407177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407177).length < 2 ^ (prefixWord ++ tailWord_6407177).sum := by decide
  have hdescent : baseEnd_6407177 < baseStart_6407177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407227 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_6407227 : Nat := 118140960795 + 6407227 * 2 ^ 59
def prefixEnd_6407227 : Nat := 4983230072969 + 3 ^ 40 * 6407227 * 2
def baseEnd_6407227 : Nat := 3289987113465108428596205

theorem tailTrace_6407227 : CollatzResearch.WordTrace tailWord_6407227 prefixEnd_6407227 3289987113465108428596205 := by
  unfold tailWord_6407227
  simp only [CollatzResearch.WordTrace]
  refine ⟨233690767158718321097643935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155793844772478880731762623 233690767158718321097643935)
  ·
    refine ⟨350536150738077481646465903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233690767158718321097643935 350536150738077481646465903)
    ·
      refine ⟨525804226107116222469698855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350536150738077481646465903 525804226107116222469698855)
      ·
        refine ⟨788706339160674333704548283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525804226107116222469698855 788706339160674333704548283)
        ·
          refine ⟨1183059508741011500556822425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788706339160674333704548283 1183059508741011500556822425)
          ·
            refine ⟨887294631555758625417616819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183059508741011500556822425 887294631555758625417616819)
            ·
              refine ⟨1330941947333637938126425229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887294631555758625417616819 1330941947333637938126425229)
              ·
                refine ⟨499103230250114226797409461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330941947333637938126425229 499103230250114226797409461)
                ·
                  refine ⟨46790927835948208762257137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499103230250114226797409461 46790927835948208762257137)
                  ·
                    refine ⟨35093195876961156571692853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46790927835948208762257137 35093195876961156571692853)
                    ·
                      refine ⟨3289987113465108428596205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35093195876961156571692853 3289987113465108428596205)
                      ·
                        rfl

theorem cell23_6407227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_6407227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407227 prefixEnd_6407227 := by exact prefixLift 6407227
  have htrace : WordTrace (prefixWord ++ tailWord_6407227) baseStart_6407227 baseEnd_6407227 := by
    simpa [prefixWord, tailWord_6407227, baseEnd_6407227] using wordTrace_append hprefix tailTrace_6407227
  have hstable : (prefixWord ++ tailWord_6407227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407227).length < 2 ^ (prefixWord ++ tailWord_6407227).sum := by decide
  have hdescent : baseEnd_6407227 < baseStart_6407227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407271 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_6407271 : Nat := 118140960795 + 6407271 * 2 ^ 59
def prefixEnd_6407271 : Nat := 4983230072969 + 3 ^ 40 * 6407271 * 2
def baseEnd_6407271 : Nat := 3290009706613906256446003

theorem tailTrace_6407271 : CollatzResearch.WordTrace tailWord_6407271 prefixEnd_6407271 3290009706613906256446003 := by
  unfold tailWord_6407271
  simp only [CollatzResearch.WordTrace]
  refine ⟨233692371970558916612245667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155794914647039277741497111 233692371970558916612245667)
  ·
    refine ⟨350538557955838374918368501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233692371970558916612245667 350538557955838374918368501)
    ·
      refine ⟨32862989808359847648597047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 350538557955838374918368501 32862989808359847648597047)
      ·
        refine ⟨49294484712539771472895571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32862989808359847648597047 49294484712539771472895571)
        ·
          refine ⟨73941727068809657209343357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49294484712539771472895571 73941727068809657209343357)
          ·
            refine ⟨27728147650803621453503759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73941727068809657209343357 27728147650803621453503759)
            ·
              refine ⟨41592221476205432180255639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27728147650803621453503759 41592221476205432180255639)
              ·
                refine ⟨62388332214308148270383459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41592221476205432180255639 62388332214308148270383459)
                ·
                  refine ⟨93582498321462222405575189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62388332214308148270383459 93582498321462222405575189)
                  ·
                    refine ⟨4386679608818541675261337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93582498321462222405575189 4386679608818541675261337)
                    ·
                      refine ⟨3290009706613906256446003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386679608818541675261337 3290009706613906256446003)
                      ·
                        rfl

theorem cell23_6407271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_6407271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407271 prefixEnd_6407271 := by exact prefixLift 6407271
  have htrace : WordTrace (prefixWord ++ tailWord_6407271) baseStart_6407271 baseEnd_6407271 := by
    simpa [prefixWord, tailWord_6407271, baseEnd_6407271] using wordTrace_append hprefix tailTrace_6407271
  have hstable : (prefixWord ++ tailWord_6407271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407271).length < 2 ^ (prefixWord ++ tailWord_6407271).sum := by decide
  have hdescent : baseEnd_6407271 < baseStart_6407271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407285 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_6407285 : Nat := 118140960795 + 6407285 * 2 ^ 59
def prefixEnd_6407285 : Nat := 4983230072969 + 3 ^ 40 * 6407285 * 2
def baseEnd_6407285 : Nat := 1096672298447689733890313

theorem tailTrace_6407285 : CollatzResearch.WordTrace tailWord_6407285 prefixEnd_6407285 1096672298447689733890313 := by
  unfold tailWord_6407285
  simp only [CollatzResearch.WordTrace]
  refine ⟨233692882592508197003255309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155795255061672131335503539 233692882592508197003255309)
  ·
    refine ⟨87634830972190573876220741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233692882592508197003255309 87634830972190573876220741)
    ·
      refine ⟨16431530807285732601791389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87634830972190573876220741 16431530807285732601791389)
      ·
        refine ⟨6161824052732149725671771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16431530807285732601791389 6161824052732149725671771)
        ·
          refine ⟨9242736079098224588507657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161824052732149725671771 9242736079098224588507657)
          ·
            refine ⟨6932052059323668441380743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9242736079098224588507657 6932052059323668441380743)
            ·
              refine ⟨10398078088985502662071115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932052059323668441380743 10398078088985502662071115)
              ·
                refine ⟨15597117133478253993106673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10398078088985502662071115 15597117133478253993106673)
                ·
                  refine ⟨11697837850108690494830005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15597117133478253993106673 11697837850108690494830005)
                  ·
                    refine ⟨1096672298447689733890313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11697837850108690494830005 1096672298447689733890313)
                    ·
                      rfl

theorem cell23_6407285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_6407285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407285 prefixEnd_6407285 := by exact prefixLift 6407285
  have htrace : WordTrace (prefixWord ++ tailWord_6407285) baseStart_6407285 baseEnd_6407285 := by
    simpa [prefixWord, tailWord_6407285, baseEnd_6407285] using wordTrace_append hprefix tailTrace_6407285
  have hstable : (prefixWord ++ tailWord_6407285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407285).length < 2 ^ (prefixWord ++ tailWord_6407285).sum := by decide
  have hdescent : baseEnd_6407285 < baseStart_6407285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407354 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_6407354 : Nat := 118140960795 + 6407354 * 2 ^ 59
def prefixEnd_6407354 : Nat := 4983230072969 + 3 ^ 40 * 6407354 * 2
def baseEnd_6407354 : Nat := 1096684108502743143902707

theorem tailTrace_6407354 : CollatzResearch.WordTrace tailWord_6407354 prefixEnd_6407354 1096684108502743143902707 := by
  unfold tailWord_6407354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58423849807314555446879279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155796932819505481191678077 58423849807314555446879279)
  ·
    refine ⟨87635774710971833170318919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58423849807314555446879279 87635774710971833170318919)
    ·
      refine ⟨131453662066457749755478379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87635774710971833170318919 131453662066457749755478379)
      ·
        refine ⟨197180493099686624633217569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131453662066457749755478379 197180493099686624633217569)
        ·
          refine ⟨147885369824764968474913177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197180493099686624633217569 147885369824764968474913177)
          ·
            refine ⟨110914027368573726356184883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147885369824764968474913177 110914027368573726356184883)
            ·
              refine ⟨166371041052860589534277325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110914027368573726356184883 166371041052860589534277325)
              ·
                refine ⟨62389140394822721075353997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166371041052860589534277325 62389140394822721075353997)
                ·
                  refine ⟨23395927648058520403257749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62389140394822721075353997 23395927648058520403257749)
                  ·
                    refine ⟨1096684108502743143902707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23395927648058520403257749 1096684108502743143902707)
                    ·
                      rfl

theorem cell23_6407354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_6407354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407354 prefixEnd_6407354 := by exact prefixLift 6407354
  have htrace : WordTrace (prefixWord ++ tailWord_6407354) baseStart_6407354 baseEnd_6407354 := by
    simpa [prefixWord, tailWord_6407354, baseEnd_6407354] using wordTrace_append hprefix tailTrace_6407354
  have hstable : (prefixWord ++ tailWord_6407354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407354).length < 2 ^ (prefixWord ++ tailWord_6407354).sum := by decide
  have hdescent : baseEnd_6407354 < baseStart_6407354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407358 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_6407358 : Nat := 118140960795 + 6407358 * 2 ^ 59
def prefixEnd_6407358 : Nat := 4983230072969 + 3 ^ 40 * 6407358 * 2
def baseEnd_6407358 : Nat := 1096684793143615805352701

theorem tailTrace_6407358 : CollatzResearch.WordTrace tailWord_6407358 prefixEnd_6407358 1096684793143615805352701 := by
  unfold tailWord_6407358
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211943140155466308832841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155797030080829153647108485 29211943140155466308832841)
  ·
    refine ⟨21908957355116599731624631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29211943140155466308832841 21908957355116599731624631)
    ·
      refine ⟨32863436032674899597436947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21908957355116599731624631 32863436032674899597436947)
      ·
        refine ⟨49295154049012349396155421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32863436032674899597436947 49295154049012349396155421)
        ·
          refine ⟨18485682768379631023558283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49295154049012349396155421 18485682768379631023558283)
          ·
            refine ⟨27728524152569446535337425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18485682768379631023558283 27728524152569446535337425)
            ·
              refine ⟨20796393114427084901503069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27728524152569446535337425 20796393114427084901503069)
              ·
                refine ⟨7798647417910156838063651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20796393114427084901503069 7798647417910156838063651)
                ·
                  refine ⟨11697971126865235257095477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798647417910156838063651 11697971126865235257095477)
                  ·
                    refine ⟨1096684793143615805352701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11697971126865235257095477 1096684793143615805352701)
                    ·
                      rfl

theorem cell23_6407358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_6407358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407358 prefixEnd_6407358 := by exact prefixLift 6407358
  have htrace : WordTrace (prefixWord ++ tailWord_6407358) baseStart_6407358 baseEnd_6407358 := by
    simpa [prefixWord, tailWord_6407358, baseEnd_6407358] using wordTrace_append hprefix tailTrace_6407358
  have hstable : (prefixWord ++ tailWord_6407358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407358).length < 2 ^ (prefixWord ++ tailWord_6407358).sum := by decide
  have hdescent : baseEnd_6407358 < baseStart_6407358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407366 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_6407366 : Nat := 118140960795 + 6407366 * 2 ^ 59
def prefixEnd_6407366 : Nat := 4983230072969 + 3 ^ 40 * 6407366 * 2
def baseEnd_6407366 : Nat := 1096686162425361128252689

theorem tailTrace_6407366 : CollatzResearch.WordTrace tailWord_6407366 prefixEnd_6407366 1096686162425361128252689 := by
  unfold tailWord_6407366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302994903287960869904811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155797224603476498557969301 7302994903287960869904811)
  ·
    refine ⟨10954492354931941304857217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7302994903287960869904811 10954492354931941304857217)
    ·
      refine ⟨8215869266198955978642913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10954492354931941304857217 8215869266198955978642913)
      ·
        refine ⟨6161901949649216983982185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8215869266198955978642913 6161901949649216983982185)
        ·
          refine ⟨4621426462236912737986639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161901949649216983982185 4621426462236912737986639)
          ·
            refine ⟨6932139693355369106979959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621426462236912737986639 6932139693355369106979959)
            ·
              refine ⟨10398209540033053660469939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932139693355369106979959 10398209540033053660469939)
              ·
                refine ⟨15597314310049580490704909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10398209540033053660469939 15597314310049580490704909)
                ·
                  refine ⟨5848992866268592684014341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15597314310049580490704909 5848992866268592684014341)
                  ·
                    refine ⟨1096686162425361128252689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848992866268592684014341 1096686162425361128252689)
                    ·
                      rfl

theorem cell23_6407366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_6407366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407366 prefixEnd_6407366 := by exact prefixLift 6407366
  have htrace : WordTrace (prefixWord ++ tailWord_6407366) baseStart_6407366 baseEnd_6407366 := by
    simpa [prefixWord, tailWord_6407366, baseEnd_6407366] using wordTrace_append hprefix tailTrace_6407366
  have hstable : (prefixWord ++ tailWord_6407366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407366).length < 2 ^ (prefixWord ++ tailWord_6407366).sum := by decide
  have hdescent : baseEnd_6407366 < baseStart_6407366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407411 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 3]
def baseStart_6407411 : Nat := 118140960795 + 6407411 * 2 ^ 59
def prefixEnd_6407411 : Nat := 4983230072969 + 3 ^ 40 * 6407411 * 2
def baseEnd_6407411 : Nat := 3290081593905535708695359

theorem tailTrace_6407411 : CollatzResearch.WordTrace tailWord_6407411 prefixEnd_6407411 3290081593905535708695359 := by
  unfold tailWord_6407411
  simp only [CollatzResearch.WordTrace]
  refine ⟨233697478190051720522342087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155798318793367813681561391 233697478190051720522342087)
  ·
    refine ⟨350546217285077580783513131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233697478190051720522342087 350546217285077580783513131)
    ·
      refine ⟨525819325927616371175269697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350546217285077580783513131 525819325927616371175269697)
      ·
        refine ⟨394364494445712278381452273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525819325927616371175269697 394364494445712278381452273)
        ·
          refine ⟨295773370834284208786089205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394364494445712278381452273 295773370834284208786089205)
          ·
            refine ⟨27728753515714144573695863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295773370834284208786089205 27728753515714144573695863)
            ·
              refine ⟨41593130273571216860543795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27728753515714144573695863 41593130273571216860543795)
              ·
                refine ⟨62389695410356825290815693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41593130273571216860543795 62389695410356825290815693)
                ·
                  refine ⟨23396135778883809484055885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62389695410356825290815693 23396135778883809484055885)
                  ·
                    refine ⟨8773550917081428556520957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23396135778883809484055885 8773550917081428556520957)
                    ·
                      refine ⟨3290081593905535708695359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8773550917081428556520957 3290081593905535708695359)
                      ·
                        rfl

theorem cell23_6407411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_6407411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407411 prefixEnd_6407411 := by exact prefixLift 6407411
  have htrace : WordTrace (prefixWord ++ tailWord_6407411) baseStart_6407411 baseEnd_6407411 := by
    simpa [prefixWord, tailWord_6407411, baseEnd_6407411] using wordTrace_append hprefix tailTrace_6407411
  have hstable : (prefixWord ++ tailWord_6407411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407411).length < 2 ^ (prefixWord ++ tailWord_6407411).sum := by decide
  have hdescent : baseEnd_6407411 < baseStart_6407411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407442 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6407442 : Nat := 118140960795 + 6407442 * 2 ^ 59
def prefixEnd_6407442 : Nat := 4983230072969 + 3 ^ 40 * 6407442 * 2
def baseEnd_6407442 : Nat := 3290097511805825087407717

theorem tailTrace_6407442 : CollatzResearch.WordTrace tailWord_6407442 prefixEnd_6407442 3290097511805825087407717 := by
  unfold tailWord_6407442
  simp only [CollatzResearch.WordTrace]
  refine ⟨58424652213234853204180145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155799072568626275211147053 58424652213234853204180145)
  ·
    refine ⟨43818489159926139903135109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58424652213234853204180145 43818489159926139903135109)
    ·
      refine ⟨8215966717486151231837833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43818489159926139903135109 8215966717486151231837833)
      ·
        refine ⟨6161975038114613423878375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8215966717486151231837833 6161975038114613423878375)
        ·
          refine ⟨9242962557171920135817563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161975038114613423878375 9242962557171920135817563)
          ·
            refine ⟨13864443835757880203726345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242962557171920135817563 13864443835757880203726345)
            ·
              refine ⟨10398332876818410152794759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13864443835757880203726345 10398332876818410152794759)
              ·
                refine ⟨15597499315227615229192139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10398332876818410152794759 15597499315227615229192139)
                ·
                  refine ⟨23396248972841422843788209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15597499315227615229192139 23396248972841422843788209)
                  ·
                    refine ⟨17547186729631067132841157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23396248972841422843788209 17547186729631067132841157)
                    ·
                      refine ⟨3290097511805825087407717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17547186729631067132841157 3290097511805825087407717)
                      ·
                        rfl

theorem cell23_6407442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6407442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407442 prefixEnd_6407442 := by exact prefixLift 6407442
  have htrace : WordTrace (prefixWord ++ tailWord_6407442) baseStart_6407442 baseEnd_6407442 := by
    simpa [prefixWord, tailWord_6407442, baseEnd_6407442] using wordTrace_append hprefix tailTrace_6407442
  have hstable : (prefixWord ++ tailWord_6407442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407442).length < 2 ^ (prefixWord ++ tailWord_6407442).sum := by decide
  have hdescent : baseEnd_6407442 < baseStart_6407442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407521 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_6407521 : Nat := 118140960795 + 6407521 * 2 ^ 59
def prefixEnd_6407521 : Nat := 4983230072969 + 3 ^ 40 * 6407521 * 2
def baseEnd_6407521 : Nat := 1096712692259176759439951

theorem tailTrace_6407521 : CollatzResearch.WordTrace tailWord_6407521 prefixEnd_6407521 1096712692259176759439951 := by
  unfold tailWord_6407521
  simp only [CollatzResearch.WordTrace]
  refine ⟨233701490219653209308846417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155800993479768806205897611 233701490219653209308846417)
  ·
    refine ⟨175276117664739906981634813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233701490219653209308846417 175276117664739906981634813)
    ·
      refine ⟨65728544124277465118113055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175276117664739906981634813 65728544124277465118113055)
      ·
        refine ⟨98592816186416197677169583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65728544124277465118113055 98592816186416197677169583)
        ·
          refine ⟨147889224279624296515754375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98592816186416197677169583 147889224279624296515754375)
          ·
            refine ⟨221833836419436444773631563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147889224279624296515754375 221833836419436444773631563)
            ·
              refine ⟨332750754629154667160447345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221833836419436444773631563 332750754629154667160447345)
              ·
                refine ⟨249563065971866000370335509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332750754629154667160447345 249563065971866000370335509)
                ·
                  refine ⟨11698268717431218767359477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249563065971866000370335509 11698268717431218767359477)
                  ·
                    refine ⟨1096712692259176759439951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11698268717431218767359477 1096712692259176759439951)
                    ·
                      rfl

theorem cell23_6407521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_6407521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407521 prefixEnd_6407521 := by exact prefixLift 6407521
  have htrace : WordTrace (prefixWord ++ tailWord_6407521) baseStart_6407521 baseEnd_6407521 := by
    simpa [prefixWord, tailWord_6407521, baseEnd_6407521] using wordTrace_append hprefix tailTrace_6407521
  have hstable : (prefixWord ++ tailWord_6407521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407521).length < 2 ^ (prefixWord ++ tailWord_6407521).sum := by decide
  have hdescent : baseEnd_6407521 < baseStart_6407521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407538 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_6407538 : Nat := 118140960795 + 6407538 * 2 ^ 59
def prefixEnd_6407538 : Nat := 4983230072969 + 3 ^ 40 * 6407538 * 2
def baseEnd_6407538 : Nat := 1096715601982885570602425

theorem tailTrace_6407538 : CollatzResearch.WordTrace tailWord_6407538 prefixEnd_6407538 1096715601982885570602425 := by
  unfold tailWord_6407538
  simp only [CollatzResearch.WordTrace]
  refine ⟨58425527565147905303053817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155801406840394414141476845 58425527565147905303053817)
  ·
    refine ⟨43819145673860928977290363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58425527565147905303053817 43819145673860928977290363)
    ·
      refine ⟨65728718510791393465935545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43819145673860928977290363 65728718510791393465935545)
      ·
        refine ⟨49296538883093545099451659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65728718510791393465935545 49296538883093545099451659)
        ·
          refine ⟨73944808324640317649177489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49296538883093545099451659 73944808324640317649177489)
          ·
            refine ⟨55458606243480238236883117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73944808324640317649177489 55458606243480238236883117)
            ·
              refine ⟨20796977341305089338831169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55458606243480238236883117 20796977341305089338831169)
              ·
                refine ⟨15597733005978817004123377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20796977341305089338831169 15597733005978817004123377)
                ·
                  refine ⟨11698299754484112753092533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15597733005978817004123377 11698299754484112753092533)
                  ·
                    refine ⟨1096715601982885570602425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11698299754484112753092533 1096715601982885570602425)
                    ·
                      rfl

theorem cell23_6407538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_6407538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407538 prefixEnd_6407538 := by exact prefixLift 6407538
  have htrace : WordTrace (prefixWord ++ tailWord_6407538) baseStart_6407538 baseEnd_6407538 := by
    simpa [prefixWord, tailWord_6407538, baseEnd_6407538] using wordTrace_append hprefix tailTrace_6407538
  have hstable : (prefixWord ++ tailWord_6407538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407538).length < 2 ^ (prefixWord ++ tailWord_6407538).sum := by decide
  have hdescent : baseEnd_6407538 < baseStart_6407538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407553 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_6407553 : Nat := 118140960795 + 6407553 * 2 ^ 59
def prefixEnd_6407553 : Nat := 4983230072969 + 3 ^ 40 * 6407553 * 2
def baseEnd_6407553 : Nat := 3290154508158474153119707

theorem tailTrace_6407553 : CollatzResearch.WordTrace tailWord_6407553 prefixEnd_6407553 3290154508158474153119707 := by
  unfold tailWord_6407553
  simp only [CollatzResearch.WordTrace]
  refine ⟨233702657355537278774011313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155801771570358185849340875 233702657355537278774011313)
  ·
    refine ⟨175276993016652959080508485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233702657355537278774011313 175276993016652959080508485)
    ·
      refine ⟨32864436190622429827595341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175276993016652959080508485 32864436190622429827595341)
      ·
        refine ⟨12324163571483411185348253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32864436190622429827595341 12324163571483411185348253)
        ·
          refine ⟨4621561339306279194505595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12324163571483411185348253 4621561339306279194505595)
          ·
            refine ⟨6932342008959418791758393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621561339306279194505595 6932342008959418791758393)
            ·
              refine ⟨5199256506719564093818795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932342008959418791758393 5199256506719564093818795)
              ·
                refine ⟨7798884760079346140728193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199256506719564093818795 7798884760079346140728193)
                ·
                  refine ⟨5849163570059509605546145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7798884760079346140728193 5849163570059509605546145)
                  ·
                    refine ⟨4386872677544632204159609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5849163570059509605546145 4386872677544632204159609)
                    ·
                      refine ⟨3290154508158474153119707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4386872677544632204159609 3290154508158474153119707)
                      ·
                        rfl

theorem cell23_6407553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_6407553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407553 prefixEnd_6407553 := by exact prefixLift 6407553
  have htrace : WordTrace (prefixWord ++ tailWord_6407553) baseStart_6407553 baseEnd_6407553 := by
    simpa [prefixWord, tailWord_6407553, baseEnd_6407553] using wordTrace_append hprefix tailTrace_6407553
  have hstable : (prefixWord ++ tailWord_6407553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407553).length < 2 ^ (prefixWord ++ tailWord_6407553).sum := by decide
  have hdescent : baseEnd_6407553 < baseStart_6407553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407648 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_6407648 : Nat := 118140960795 + 6407648 * 2 ^ 59
def prefixEnd_6407648 : Nat := 4983230072969 + 3 ^ 40 * 6407648 * 2
def baseEnd_6407648 : Nat := 3290203288820651281431769

theorem tailTrace_6407648 : CollatzResearch.WordTrace tailWord_6407648 prefixEnd_6407648 3290203288820651281431769 := by
  unfold tailWord_6407648
  simp only [CollatzResearch.WordTrace]
  refine ⟨116853061145096554999359799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155804081526795406665813065 116853061145096554999359799)
  ·
    refine ⟨175279591717644832499039699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116853061145096554999359799 175279591717644832499039699)
    ·
      refine ⟨262919387576467248748559549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175279591717644832499039699 262919387576467248748559549)
      ·
        refine ⟨98594770341175218280709831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262919387576467248748559549 98594770341175218280709831)
        ·
          refine ⟨147892155511762827421064747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98594770341175218280709831 147892155511762827421064747)
          ·
            refine ⟨221838233267644241131597121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147892155511762827421064747 221838233267644241131597121)
            ·
              refine ⟨166378674950733180848697841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221838233267644241131597121 166378674950733180848697841)
              ·
                refine ⟨124784006213049885636523381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166378674950733180848697841 124784006213049885636523381)
                ·
                  refine ⟨11698500582473426778424067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124784006213049885636523381 11698500582473426778424067)
                  ·
                    refine ⟨17547750873710140167636101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11698500582473426778424067 17547750873710140167636101)
                    ·
                      refine ⟨3290203288820651281431769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17547750873710140167636101 3290203288820651281431769)
                      ·
                        rfl

theorem cell23_6407648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_6407648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407648 prefixEnd_6407648 := by exact prefixLift 6407648
  have htrace : WordTrace (prefixWord ++ tailWord_6407648) baseStart_6407648 baseEnd_6407648 := by
    simpa [prefixWord, tailWord_6407648, baseEnd_6407648] using wordTrace_append hprefix tailTrace_6407648
  have hstable : (prefixWord ++ tailWord_6407648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407648).length < 2 ^ (prefixWord ++ tailWord_6407648).sum := by decide
  have hdescent : baseEnd_6407648 < baseStart_6407648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407710 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6407710 : Nat := 118140960795 + 6407710 * 2 ^ 59
def prefixEnd_6407710 : Nat := 4983230072969 + 3 ^ 40 * 6407710 * 2
def baseEnd_6407710 : Nat := 3290235124621230038856485

theorem tailTrace_6407710 : CollatzResearch.WordTrace tailWord_6407710 prefixEnd_6407710 3290235124621230038856485 := by
  unfold tailWord_6407710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29213547951996061823434573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155805589077312329724984389 29213547951996061823434573)
  ·
    refine ⟨10955080481998523183787965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29213547951996061823434573 10955080481998523183787965)
    ·
      refine ⟨4108155180749446193920487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10955080481998523183787965 4108155180749446193920487)
      ·
        refine ⟨6162232771124169290880731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108155180749446193920487 6162232771124169290880731)
        ·
          refine ⟨9243349156686253936321097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162232771124169290880731 9243349156686253936321097)
          ·
            refine ⟨6932511867514690452240823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9243349156686253936321097 6932511867514690452240823)
            ·
              refine ⟨10398767801272035678361235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932511867514690452240823 10398767801272035678361235)
              ·
                refine ⟨15598151701908053517541853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10398767801272035678361235 15598151701908053517541853)
                ·
                  refine ⟨5849306888215520069078195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15598151701908053517541853 5849306888215520069078195)
                  ·
                    refine ⟨8773960332323280103617293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5849306888215520069078195 8773960332323280103617293)
                    ·
                      refine ⟨3290235124621230038856485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8773960332323280103617293 3290235124621230038856485)
                      ·
                        rfl

theorem cell23_6407710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6407710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407710 prefixEnd_6407710 := by exact prefixLift 6407710
  have htrace : WordTrace (prefixWord ++ tailWord_6407710) baseStart_6407710 baseEnd_6407710 := by
    simpa [prefixWord, tailWord_6407710, baseEnd_6407710] using wordTrace_append hprefix tailTrace_6407710
  have hstable : (prefixWord ++ tailWord_6407710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407710).length < 2 ^ (prefixWord ++ tailWord_6407710).sum := by decide
  have hdescent : baseEnd_6407710 < baseStart_6407710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407726 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_6407726 : Nat := 118140960795 + 6407726 * 2 ^ 59
def prefixEnd_6407726 : Nat := 4983230072969 + 3 ^ 40 * 6407726 * 2
def baseEnd_6407726 : Nat := 1096747780103900658752137

theorem tailTrace_6407726 : CollatzResearch.WordTrace tailWord_6407726 prefixEnd_6407726 1096747780103900658752137 := by
  unfold tailWord_6407726
  simp only [CollatzResearch.WordTrace]
  refine ⟨29213620897988816165007379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155805978122607019546706021 29213620897988816165007379)
  ·
    refine ⟨43820431346983224247511069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29213620897988816165007379 43820431346983224247511069)
    ·
      refine ⟨16432661755118709092816651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43820431346983224247511069 16432661755118709092816651)
      ·
        refine ⟨24648992632678063639224977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16432661755118709092816651 24648992632678063639224977)
        ·
          refine ⟨18486744474508547729418733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24648992632678063639224977 18486744474508547729418733)
          ·
            refine ⟨6932529177940705398532025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18486744474508547729418733 6932529177940705398532025)
            ·
              refine ⟨5199396883455529048899019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932529177940705398532025 5199396883455529048899019)
              ·
                refine ⟨7799095325183293573348529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199396883455529048899019 7799095325183293573348529)
                ·
                  refine ⟨5849321493887470180011397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7799095325183293573348529 5849321493887470180011397)
                  ·
                    refine ⟨1096747780103900658752137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5849321493887470180011397 1096747780103900658752137)
                    ·
                      rfl

theorem cell23_6407726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_6407726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407726 prefixEnd_6407726 := by exact prefixLift 6407726
  have htrace : WordTrace (prefixWord ++ tailWord_6407726) baseStart_6407726 baseEnd_6407726 := by
    simpa [prefixWord, tailWord_6407726, baseEnd_6407726] using wordTrace_append hprefix tailTrace_6407726
  have hstable : (prefixWord ++ tailWord_6407726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407726).length < 2 ^ (prefixWord ++ tailWord_6407726).sum := by decide
  have hdescent : baseEnd_6407726 < baseStart_6407726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407768 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6407768 : Nat := 118140960795 + 6407768 * 2 ^ 59
def prefixEnd_6407768 : Nat := 4983230072969 + 3 ^ 40 * 6407768 * 2
def baseEnd_6407768 : Nat := 3290264906499190811931217

theorem tailTrace_6407768 : CollatzResearch.WordTrace tailWord_6407768 prefixEnd_6407768 3290264906499190811931217 := by
  unfold tailWord_6407768
  simp only [CollatzResearch.WordTrace]
  refine ⟨116855249524879185246543979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155806999366505580328725305 116855249524879185246543979)
  ·
    refine ⟨175282874287318777869815969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116855249524879185246543979 175282874287318777869815969)
    ·
      refine ⟨131462155715489083402361977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175282874287318777869815969 131462155715489083402361977)
      ·
        refine ⟨98596616786616812551771483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131462155715489083402361977 98596616786616812551771483)
        ·
          refine ⟨147894925179925218827657225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98596616786616812551771483 147894925179925218827657225)
          ·
            refine ⟨110921193884943914120742919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147894925179925218827657225 110921193884943914120742919)
            ·
              refine ⟨166381790827415871181114379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110921193884943914120742919 166381790827415871181114379)
              ·
                refine ⟨249572686241123806771671569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166381790827415871181114379 249572686241123806771671569)
                ·
                  refine ⟨187179514680842855078753677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249572686241123806771671569 187179514680842855078753677)
                  ·
                    refine ⟨70192318005316070654532629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187179514680842855078753677 70192318005316070654532629)
                    ·
                      refine ⟨3290264906499190811931217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70192318005316070654532629 3290264906499190811931217)
                      ·
                        rfl

theorem cell23_6407768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6407768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407768 prefixEnd_6407768 := by exact prefixLift 6407768
  have htrace : WordTrace (prefixWord ++ tailWord_6407768) baseStart_6407768 baseEnd_6407768 := by
    simpa [prefixWord, tailWord_6407768, baseEnd_6407768] using wordTrace_append hprefix tailTrace_6407768
  have hstable : (prefixWord ++ tailWord_6407768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407768).length < 2 ^ (prefixWord ++ tailWord_6407768).sum := by decide
  have hdescent : baseEnd_6407768 < baseStart_6407768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407822 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6407822 : Nat := 118140960795 + 6407822 * 2 ^ 59
def prefixEnd_6407822 : Nat := 4983230072969 + 3 ^ 40 * 6407822 * 2
def baseEnd_6407822 : Nat := 3290292634454533600655969

theorem tailTrace_6407822 : CollatzResearch.WordTrace tailWord_6407822 prefixEnd_6407822 3290292634454533600655969 := by
  unfold tailWord_6407822
  simp only [CollatzResearch.WordTrace]
  refine ⟨29214058573945342214444215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155808312394375158477035813 29214058573945342214444215)
  ·
    refine ⟨43821087860918013321666323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29214058573945342214444215 43821087860918013321666323)
    ·
      refine ⟨65731631791377019982499485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43821087860918013321666323 65731631791377019982499485)
      ·
        refine ⟨24649361921766382493437307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65731631791377019982499485 24649361921766382493437307)
        ·
          refine ⟨36974042882649573740155961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24649361921766382493437307 36974042882649573740155961)
          ·
            refine ⟨27730532161987180305116971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36974042882649573740155961 27730532161987180305116971)
            ·
              refine ⟨41595798242980770457675457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27730532161987180305116971 41595798242980770457675457)
              ·
                refine ⟨31196848682235577843256593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41595798242980770457675457 31196848682235577843256593)
                ·
                  refine ⟨23397636511676683382442445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31196848682235577843256593 23397636511676683382442445)
                  ·
                    refine ⟨8774113691878756268415917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23397636511676683382442445 8774113691878756268415917)
                    ·
                      refine ⟨3290292634454533600655969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8774113691878756268415917 3290292634454533600655969)
                      ·
                        rfl

theorem cell23_6407822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6407822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407822 prefixEnd_6407822 := by exact prefixLift 6407822
  have htrace : WordTrace (prefixWord ++ tailWord_6407822) baseStart_6407822 baseEnd_6407822 := by
    simpa [prefixWord, tailWord_6407822, baseEnd_6407822] using wordTrace_append hprefix tailTrace_6407822
  have hstable : (prefixWord ++ tailWord_6407822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407822).length < 2 ^ (prefixWord ++ tailWord_6407822).sum := by decide
  have hdescent : baseEnd_6407822 < baseStart_6407822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407845 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_6407845 : Nat := 118140960795 + 6407845 * 2 ^ 59
def prefixEnd_6407845 : Nat := 4983230072969 + 3 ^ 40 * 6407845 * 2
def baseEnd_6407845 : Nat := 3290304444509587010668363

theorem tailTrace_6407845 : CollatzResearch.WordTrace tailWord_6407845 prefixEnd_6407845 3290304444509587010668363 := by
  unfold tailWord_6407845
  simp only [CollatzResearch.WordTrace]
  refine ⟨233713307470479412643640989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155808871646986275095760659 233713307470479412643640989)
  ·
    refine ⟨87642490301429779741365371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233713307470479412643640989 87642490301429779741365371)
    ·
      refine ⟨131463735452144669612048057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87642490301429779741365371 131463735452144669612048057)
      ·
        refine ⟨98597801589108502209036043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131463735452144669612048057 98597801589108502209036043)
        ·
          refine ⟨147896702383662753313554065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98597801589108502209036043 147896702383662753313554065)
          ·
            refine ⟨110922526787747064985165549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147896702383662753313554065 110922526787747064985165549)
            ·
              refine ⟨41595947545405149369437081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110922526787747064985165549 41595947545405149369437081)
              ·
                refine ⟨31196960659053862027077811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41595947545405149369437081 31196960659053862027077811)
                ·
                  refine ⟨46795440988580793040616717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31196960659053862027077811 46795440988580793040616717)
                  ·
                    refine ⟨17548290370717797390231269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46795440988580793040616717 17548290370717797390231269)
                    ·
                      refine ⟨3290304444509587010668363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17548290370717797390231269 3290304444509587010668363)
                      ·
                        rfl

theorem cell23_6407845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_6407845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407845 prefixEnd_6407845 := by exact prefixLift 6407845
  have htrace : WordTrace (prefixWord ++ tailWord_6407845) baseStart_6407845 baseEnd_6407845 := by
    simpa [prefixWord, tailWord_6407845, baseEnd_6407845] using wordTrace_append hprefix tailTrace_6407845
  have hstable : (prefixWord ++ tailWord_6407845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407845).length < 2 ^ (prefixWord ++ tailWord_6407845).sum := by decide
  have hdescent : baseEnd_6407845 < baseStart_6407845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407889 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 3, 4]
def baseStart_6407889 : Nat := 118140960795 + 6407889 * 2 ^ 59
def prefixEnd_6407889 : Nat := 4983230072969 + 3 ^ 40 * 6407889 * 2
def baseEnd_6407889 : Nat := 1096775679219461612839387

theorem tailTrace_6407889 : CollatzResearch.WordTrace tailWord_6407889 prefixEnd_6407889 1096775679219461612839387 := by
  unfold tailWord_6407889
  simp only [CollatzResearch.WordTrace]
  refine ⟨233714912282320008158242721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155809941521546672105495147 233714912282320008158242721)
  ·
    refine ⟨175286184211740006118682041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233714912282320008158242721 175286184211740006118682041)
    ·
      refine ⟨131464638158805004589011531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175286184211740006118682041 131464638158805004589011531)
      ·
        refine ⟨197196957238207506883517297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131464638158805004589011531 197196957238207506883517297)
        ·
          refine ⟨147897717928655630162637973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197196957238207506883517297 147897717928655630162637973)
          ·
            refine ⟨6932705527905732663873655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147897717928655630162637973 6932705527905732663873655)
            ·
              refine ⟨10399058291858598995810483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932705527905732663873655 10399058291858598995810483)
              ·
                refine ⟨15598587437787898493715725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10399058291858598995810483 15598587437787898493715725)
                ·
                  refine ⟨5849470289170461935143397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15598587437787898493715725 5849470289170461935143397)
                  ·
                    refine ⟨1096775679219461612839387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5849470289170461935143397 1096775679219461612839387)
                    ·
                      rfl

theorem cell23_6407889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_6407889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407889 prefixEnd_6407889 := by exact prefixLift 6407889
  have htrace : WordTrace (prefixWord ++ tailWord_6407889) baseStart_6407889 baseEnd_6407889 := by
    simpa [prefixWord, tailWord_6407889, baseEnd_6407889] using wordTrace_append hprefix tailTrace_6407889
  have hstable : (prefixWord ++ tailWord_6407889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407889).length < 2 ^ (prefixWord ++ tailWord_6407889).sum := by decide
  have hdescent : baseEnd_6407889 < baseStart_6407889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407939 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 2, 3, 2]
def baseStart_6407939 : Nat := 118140960795 + 6407939 * 2 ^ 59
def prefixEnd_6407939 : Nat := 4983230072969 + 3 ^ 40 * 6407939 * 2
def baseEnd_6407939 : Nat := 3290352711691109642892931

theorem tailTrace_6407939 : CollatzResearch.WordTrace tailWord_6407939 prefixEnd_6407939 3290352711691109642892931 := by
  unfold tailWord_6407939
  simp only [CollatzResearch.WordTrace]
  refine ⟨233716735932138866697562871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155811157288092577798375247 233716735932138866697562871)
  ·
    refine ⟨350575103898208300046344307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233716735932138866697562871 350575103898208300046344307)
    ·
      refine ⟨525862655847312450069516461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350575103898208300046344307 525862655847312450069516461)
      ·
        refine ⟨197198495942742168776068673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525862655847312450069516461 197198495942742168776068673)
        ·
          refine ⟨147898871957056626582051505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197198495942742168776068673 147898871957056626582051505)
          ·
            refine ⟨110924153967792469936538629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147898871957056626582051505 110924153967792469936538629)
            ·
              refine ⟨20798278868961088113100993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110924153967792469936538629 20798278868961088113100993)
              ·
                refine ⟨15598709151720816084825745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20798278868961088113100993 15598709151720816084825745)
                ·
                  refine ⟨11699031863790612063619309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15598709151720816084825745 11699031863790612063619309)
                  ·
                    refine ⟨4387136948921479523857241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11699031863790612063619309 4387136948921479523857241)
                    ·
                      refine ⟨3290352711691109642892931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387136948921479523857241 3290352711691109642892931)
                      ·
                        rfl

theorem cell23_6407939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_6407939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407939 prefixEnd_6407939 := by exact prefixLift 6407939
  have htrace : WordTrace (prefixWord ++ tailWord_6407939) baseStart_6407939 baseEnd_6407939 := by
    simpa [prefixWord, tailWord_6407939, baseEnd_6407939] using wordTrace_append hprefix tailTrace_6407939
  have hstable : (prefixWord ++ tailWord_6407939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407939).length < 2 ^ (prefixWord ++ tailWord_6407939).sum := by decide
  have hdescent : baseEnd_6407939 < baseStart_6407939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407945 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_6407945 : Nat := 118140960795 + 6407945 * 2 ^ 59
def prefixEnd_6407945 : Nat := 4983230072969 + 3 ^ 40 * 6407945 * 2
def baseEnd_6407945 : Nat := 1096785264191678873139301

theorem tailTrace_6407945 : CollatzResearch.WordTrace tailWord_6407945 prefixEnd_6407945 1096785264191678873139301 := by
  unfold tailWord_6407945
  simp only [CollatzResearch.WordTrace]
  refine ⟨233716954770117129722281289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155811303180078086481520859 233716954770117129722281289)
  ·
    refine ⟨175287716077587847291710967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233716954770117129722281289 175287716077587847291710967)
    ·
      refine ⟨262931574116381770937566451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175287716077587847291710967 262931574116381770937566451)
      ·
        refine ⟨394397361174572656406349677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262931574116381770937566451 394397361174572656406349677)
        ·
          refine ⟨147899010440464746152381129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394397361174572656406349677 147899010440464746152381129)
          ·
            refine ⟨110924257830348559614285847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147899010440464746152381129 110924257830348559614285847)
            ·
              refine ⟨166386386745522839421428771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110924257830348559614285847 166386386745522839421428771)
              ·
                refine ⟨249579580118284259132143157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166386386745522839421428771 249579580118284259132143157)
                ·
                  refine ⟨23398085636089149293638421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249579580118284259132143157 23398085636089149293638421)
                  ·
                    refine ⟨1096785264191678873139301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23398085636089149293638421 1096785264191678873139301)
                    ·
                      rfl

theorem cell23_6407945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_6407945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407945 prefixEnd_6407945 := by exact prefixLift 6407945
  have htrace : WordTrace (prefixWord ++ tailWord_6407945) baseStart_6407945 baseEnd_6407945 := by
    simpa [prefixWord, tailWord_6407945, baseEnd_6407945] using wordTrace_append hprefix tailTrace_6407945
  have hstable : (prefixWord ++ tailWord_6407945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407945).length < 2 ^ (prefixWord ++ tailWord_6407945).sum := by decide
  have hdescent : baseEnd_6407945 < baseStart_6407945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407962 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_6407962 : Nat := 118140960795 + 6407962 * 2 ^ 59
def prefixEnd_6407962 : Nat := 4983230072969 + 3 ^ 40 * 6407962 * 2
def baseEnd_6407962 : Nat := 1096788173915387684301775

theorem tailTrace_6407962 : CollatzResearch.WordTrace tailWord_6407962 prefixEnd_6407962 1096788173915387684301775 := by
  unfold tailWord_6407962
  simp only [CollatzResearch.WordTrace]
  refine ⟨58429393702763885406412535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155811716540703694417100093 58429393702763885406412535)
  ·
    refine ⟨87644090554145828109618803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58429393702763885406412535 87644090554145828109618803)
    ·
      refine ⟨131466135831218742164428205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87644090554145828109618803 131466135831218742164428205)
      ·
        refine ⟨49299800936707028311660577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131466135831218742164428205 49299800936707028311660577)
        ·
          refine ⟨36974850702530271233745433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49299800936707028311660577 36974850702530271233745433)
          ·
            refine ⟨27731138026897703425309075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36974850702530271233745433 27731138026897703425309075)
            ·
              refine ⟨41596707040346555137963613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27731138026897703425309075 41596707040346555137963613)
              ·
                refine ⟨15598765140129958176736355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41596707040346555137963613 15598765140129958176736355)
                ·
                  refine ⟨23398147710194937265104533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15598765140129958176736355 23398147710194937265104533)
                  ·
                    refine ⟨1096788173915387684301775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23398147710194937265104533 1096788173915387684301775)
                    ·
                      rfl

theorem cell23_6407962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_6407962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407962 prefixEnd_6407962 := by exact prefixLift 6407962
  have htrace : WordTrace (prefixWord ++ tailWord_6407962) baseStart_6407962 baseEnd_6407962 := by
    simpa [prefixWord, tailWord_6407962, baseEnd_6407962] using wordTrace_append hprefix tailTrace_6407962
  have hstable : (prefixWord ++ tailWord_6407962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407962).length < 2 ^ (prefixWord ++ tailWord_6407962).sum := by decide
  have hdescent : baseEnd_6407962 < baseStart_6407962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407986 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_6407986 : Nat := 118140960795 + 6407986 * 2 ^ 59
def prefixEnd_6407986 : Nat := 4983230072969 + 3 ^ 40 * 6407986 * 2
def baseEnd_6407986 : Nat := 3290376845281870959005215

theorem tailTrace_6407986 : CollatzResearch.WordTrace tailWord_6407986 prefixEnd_6407986 3290376845281870959005215 := by
  unfold tailWord_6407986
  simp only [CollatzResearch.WordTrace]
  refine ⟨58429612540742148431130953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155812300108645729149682541 58429612540742148431130953)
  ·
    refine ⟨43822209405556611323348215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58429612540742148431130953 43822209405556611323348215)
    ·
      refine ⟨65733314108334916985022323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43822209405556611323348215 65733314108334916985022323)
      ·
        refine ⟨98599971162502375477533485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65733314108334916985022323 98599971162502375477533485)
        ·
          refine ⟨36974989185938390804075057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98599971162502375477533485 36974989185938390804075057)
          ·
            refine ⟨27731241889453793103056293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36974989185938390804075057 27731241889453793103056293)
            ·
              refine ⟨5199607854272586206823055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27731241889453793103056293 5199607854272586206823055)
              ·
                refine ⟨7799411781408879310234583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199607854272586206823055 7799411781408879310234583)
                ·
                  refine ⟨11699117672113318965351875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7799411781408879310234583 11699117672113318965351875)
                  ·
                    refine ⟨17548676508169978448027813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11699117672113318965351875 17548676508169978448027813)
                    ·
                      refine ⟨3290376845281870959005215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17548676508169978448027813 3290376845281870959005215)
                      ·
                        rfl

theorem cell23_6407986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_6407986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6407986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6407986 prefixEnd_6407986 := by exact prefixLift 6407986
  have htrace : WordTrace (prefixWord ++ tailWord_6407986) baseStart_6407986 baseEnd_6407986 := by
    simpa [prefixWord, tailWord_6407986, baseEnd_6407986] using wordTrace_append hprefix tailTrace_6407986
  have hstable : (prefixWord ++ tailWord_6407986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407986).length < 2 ^ (prefixWord ++ tailWord_6407986).sum := by decide
  have hdescent : baseEnd_6407986 < baseStart_6407986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408003 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 1, 2, 2]
def baseStart_6408003 : Nat := 118140960795 + 6408003 * 2 ^ 59
def prefixEnd_6408003 : Nat := 4983230072969 + 3 ^ 40 * 6408003 * 2
def baseEnd_6408003 : Nat := 3290385574452997392492637

theorem tailTrace_6408003 : CollatzResearch.WordTrace tailWord_6408003 prefixEnd_6408003 3290385574452997392492637 := by
  unfold tailWord_6408003
  simp only [CollatzResearch.WordTrace]
  refine ⟨233719070203907005627892663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155812713469271337085261775 233719070203907005627892663)
  ·
    refine ⟨350578605305860508441838995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233719070203907005627892663 350578605305860508441838995)
    ·
      refine ⟨525867907958790762662758493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350578605305860508441838995 525867907958790762662758493)
      ·
        refine ⟨197200465484546535998534435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525867907958790762662758493 197200465484546535998534435)
        ·
          refine ⟨295800698226819803997801653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197200465484546535998534435 295800698226819803997801653)
          ·
            refine ⟨27731315458764356624793905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295800698226819803997801653 27731315458764356624793905)
            ·
              refine ⟨20798486594073267468595429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27731315458764356624793905 20798486594073267468595429)
              ·
                refine ⟨3899716236388737650361643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20798486594073267468595429 3899716236388737650361643)
                ·
                  refine ⟨5849574354583106475542465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899716236388737650361643 5849574354583106475542465)
                  ·
                    refine ⟨4387180765937329856656849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5849574354583106475542465 4387180765937329856656849)
                    ·
                      refine ⟨3290385574452997392492637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387180765937329856656849 3290385574452997392492637)
                      ·
                        rfl

theorem cell23_6408003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_6408003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408003 prefixEnd_6408003 := by exact prefixLift 6408003
  have htrace : WordTrace (prefixWord ++ tailWord_6408003) baseStart_6408003 baseEnd_6408003 := by
    simpa [prefixWord, tailWord_6408003, baseEnd_6408003] using wordTrace_append hprefix tailTrace_6408003
  have hstable : (prefixWord ++ tailWord_6408003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408003).length < 2 ^ (prefixWord ++ tailWord_6408003).sum := by decide
  have hdescent : baseEnd_6408003 < baseStart_6408003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408006 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6408006 : Nat := 118140960795 + 6408006 * 2 ^ 59
def prefixEnd_6408006 : Nat := 4983230072969 + 3 ^ 40 * 6408006 * 2
def baseEnd_6408006 : Nat := 3290387114894960880755123

theorem tailTrace_6408006 : CollatzResearch.WordTrace tailWord_6408006 prefixEnd_6408006 3290387114894960880755123 := by
  unfold tailWord_6408006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303724363215504285632871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155812786415264091426834581 7303724363215504285632871)
  ·
    refine ⟨10955586544823256428449307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7303724363215504285632871 10955586544823256428449307)
    ·
      refine ⟨16433379817234884642673961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10955586544823256428449307 16433379817234884642673961)
      ·
        refine ⟨12325034862926163482005471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16433379817234884642673961 12325034862926163482005471)
        ·
          refine ⟨18487552294389245223008207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12325034862926163482005471 18487552294389245223008207)
          ·
            refine ⟨27731328441583867834512311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18487552294389245223008207 27731328441583867834512311)
            ·
              refine ⟨41596992662375801751768467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27731328441583867834512311 41596992662375801751768467)
              ·
                refine ⟨62395488993563702627652701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41596992662375801751768467 62395488993563702627652701)
                ·
                  refine ⟨23398308372586388485369763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62395488993563702627652701 23398308372586388485369763)
                  ·
                    refine ⟨35097462558879582728054645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23398308372586388485369763 35097462558879582728054645)
                    ·
                      refine ⟨3290387114894960880755123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35097462558879582728054645 3290387114894960880755123)
                      ·
                        rfl

theorem cell23_6408006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6408006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408006 prefixEnd_6408006 := by exact prefixLift 6408006
  have htrace : WordTrace (prefixWord ++ tailWord_6408006) baseStart_6408006 baseEnd_6408006 := by
    simpa [prefixWord, tailWord_6408006, baseEnd_6408006] using wordTrace_append hprefix tailTrace_6408006
  have hstable : (prefixWord ++ tailWord_6408006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408006).length < 2 ^ (prefixWord ++ tailWord_6408006).sum := by decide
  have hdescent : baseEnd_6408006 < baseStart_6408006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408032 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_6408032 : Nat := 118140960795 + 6408032 * 2 ^ 59
def prefixEnd_6408032 : Nat := 4983230072969 + 3 ^ 40 * 6408032 * 2
def baseEnd_6408032 : Nat := 3290400465391977779030003

theorem tailTrace_6408032 : CollatzResearch.WordTrace tailWord_6408032 prefixEnd_6408032 3290400465391977779030003 := by
  unfold tailWord_6408032
  simp only [CollatzResearch.WordTrace]
  refine ⟨116860063960400971790349175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155813418613867962387132233 116860063960400971790349175)
  ·
    refine ⟨175290095940601457685523763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116860063960400971790349175 175290095940601457685523763)
    ·
      refine ⟨262935143910902186528285645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175290095940601457685523763 262935143910902186528285645)
      ·
        refine ⟨98600678966588319948107117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262935143910902186528285645 98600678966588319948107117)
        ·
          refine ⟨36975254612470619980540169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98600678966588319948107117 36975254612470619980540169)
          ·
            refine ⟨27731440959352964985405127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36975254612470619980540169 27731440959352964985405127)
            ·
              refine ⟨41597161439029447478107691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27731440959352964985405127 41597161439029447478107691)
              ·
                refine ⟨62395742158544171217161537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41597161439029447478107691 62395742158544171217161537)
                ·
                  refine ⟨46796806618908128412871153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62395742158544171217161537 46796806618908128412871153)
                  ·
                    refine ⟨35097604964181096309653365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46796806618908128412871153 35097604964181096309653365)
                    ·
                      refine ⟨3290400465391977779030003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35097604964181096309653365 3290400465391977779030003)
                      ·
                        rfl

theorem cell23_6408032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_6408032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408032 prefixEnd_6408032 := by exact prefixLift 6408032
  have htrace : WordTrace (prefixWord ++ tailWord_6408032) baseStart_6408032 baseEnd_6408032 := by
    simpa [prefixWord, tailWord_6408032, baseEnd_6408032] using wordTrace_append hprefix tailTrace_6408032
  have hstable : (prefixWord ++ tailWord_6408032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408032).length < 2 ^ (prefixWord ++ tailWord_6408032).sum := by decide
  have hdescent : baseEnd_6408032 < baseStart_6408032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408054 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6408054 : Nat := 118140960795 + 6408054 * 2 ^ 59
def prefixEnd_6408054 : Nat := 4983230072969 + 3 ^ 40 * 6408054 * 2
def baseEnd_6408054 : Nat := 3290411761966376692954903

theorem tailTrace_6408054 : CollatzResearch.WordTrace tailWord_6408054 prefixEnd_6408054 3290411761966376692954903 := by
  unfold tailWord_6408054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607558145420140083624951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155813953551148160891999477 14607558145420140083624951)
  ·
    refine ⟨21911337218130210125437427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14607558145420140083624951 21911337218130210125437427)
    ·
      refine ⟨32867005827195315188156141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21911337218130210125437427 32867005827195315188156141)
      ·
        refine ⟨12325127185198243195558553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32867005827195315188156141 12325127185198243195558553)
        ·
          refine ⟨9243845388898682396668915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12325127185198243195558553 9243845388898682396668915)
          ·
            refine ⟨13865768083348023595003373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243845388898682396668915 13865768083348023595003373)
            ·
              refine ⟨5199663031255508848126265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13865768083348023595003373 5199663031255508848126265)
              ·
                refine ⟨3899747273441631636094699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5199663031255508848126265 3899747273441631636094699)
                ·
                  refine ⟨5849620910162447454142049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899747273441631636094699 5849620910162447454142049)
                  ·
                    refine ⟨4387215682621835590606537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5849620910162447454142049 4387215682621835590606537)
                    ·
                      refine ⟨3290411761966376692954903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387215682621835590606537 3290411761966376692954903)
                      ·
                        rfl

theorem cell23_6408054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6408054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408054 prefixEnd_6408054 := by exact prefixLift 6408054
  have htrace : WordTrace (prefixWord ++ tailWord_6408054) baseStart_6408054 baseEnd_6408054 := by
    simpa [prefixWord, tailWord_6408054, baseEnd_6408054] using wordTrace_append hprefix tailTrace_6408054
  have hstable : (prefixWord ++ tailWord_6408054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408054).length < 2 ^ (prefixWord ++ tailWord_6408054).sum := by decide
  have hdescent : baseEnd_6408054 < baseStart_6408054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408099 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 5]
def baseStart_6408099 : Nat := 118140960795 + 6408099 * 2 ^ 59
def prefixEnd_6408099 : Nat := 4983230072969 + 3 ^ 40 * 6408099 * 2
def baseEnd_6408099 : Nat := 365603874288425446321355

theorem tailTrace_6408099 : CollatzResearch.WordTrace tailWord_6408099 prefixEnd_6408099 365603874288425446321355 := by
  unfold tailWord_6408099
  simp only [CollatzResearch.WordTrace]
  refine ⟨233722571611559214023387351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155815047741039476015591567 233722571611559214023387351)
  ·
    refine ⟨350583857417338821035081027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233722571611559214023387351 350583857417338821035081027)
    ·
      refine ⟨525875786126008231552621541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350583857417338821035081027 525875786126008231552621541)
      ·
        refine ⟨98601709898626543416116539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 525875786126008231552621541 98601709898626543416116539)
        ·
          refine ⟨147902564847939815124174809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98601709898626543416116539 147902564847939815124174809)
          ·
            refine ⟨110926923635954861343131107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147902564847939815124174809 110926923635954861343131107)
            ·
              refine ⟨166390385453932292014696661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110926923635954861343131107 166390385453932292014696661)
              ·
                refine ⟨3899774659076538094094453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166390385453932292014696661 3899774659076538094094453)
                ·
                  refine ⟨365603874288425446321355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3899774659076538094094453 365603874288425446321355)
                  ·
                    rfl

theorem cell23_6408099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 5].length) (baseStart_6408099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408099 prefixEnd_6408099 := by exact prefixLift 6408099
  have htrace : WordTrace (prefixWord ++ tailWord_6408099) baseStart_6408099 baseEnd_6408099 := by
    simpa [prefixWord, tailWord_6408099, baseEnd_6408099] using wordTrace_append hprefix tailTrace_6408099
  have hstable : (prefixWord ++ tailWord_6408099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408099).length < 2 ^ (prefixWord ++ tailWord_6408099).sum := by decide
  have hdescent : baseEnd_6408099 < baseStart_6408099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408122 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_6408122 : Nat := 118140960795 + 6408122 * 2 ^ 59
def prefixEnd_6408122 : Nat := 4983230072969 + 3 ^ 40 * 6408122 * 2
def baseEnd_6408122 : Nat := 3290446678650882426904589

theorem tailTrace_6408122 : CollatzResearch.WordTrace tailWord_6408122 prefixEnd_6408122 3290446678650882426904589 := by
  unfold tailWord_6408122
  simp only [CollatzResearch.WordTrace]
  refine ⟨58430852622618972237868655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155815606993650592634316413 58430852622618972237868655)
  ·
    refine ⟨87646278933928458356802983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58430852622618972237868655 87646278933928458356802983)
    ·
      refine ⟨131469418400892687535204475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87646278933928458356802983 131469418400892687535204475)
      ·
        refine ⟨197204127601339031302806713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131469418400892687535204475 197204127601339031302806713)
        ·
          refine ⟨147903095701004273477105035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197204127601339031302806713 147903095701004273477105035)
          ·
            refine ⟨221854643551506410215657553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147903095701004273477105035 221854643551506410215657553)
            ·
              refine ⟨166390982663629807661743165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221854643551506410215657553 166390982663629807661743165)
              ·
                refine ⟨62396618498861177873153687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166390982663629807661743165 62396618498861177873153687)
                ·
                  refine ⟨93594927748291766809730531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62396618498861177873153687 93594927748291766809730531)
                  ·
                    refine ⟨140392391622437650214595797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93594927748291766809730531 140392391622437650214595797)
                    ·
                      refine ⟨3290446678650882426904589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140392391622437650214595797 3290446678650882426904589)
                      ·
                        rfl

theorem cell23_6408122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_6408122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408122 prefixEnd_6408122 := by exact prefixLift 6408122
  have htrace : WordTrace (prefixWord ++ tailWord_6408122) baseStart_6408122 baseEnd_6408122 := by
    simpa [prefixWord, tailWord_6408122, baseEnd_6408122] using wordTrace_append hprefix tailTrace_6408122
  have hstable : (prefixWord ++ tailWord_6408122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408122).length < 2 ^ (prefixWord ++ tailWord_6408122).sum := by decide
  have hdescent : baseEnd_6408122 < baseStart_6408122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408126 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_6408126 : Nat := 118140960795 + 6408126 * 2 ^ 59
def prefixEnd_6408126 : Nat := 4983230072969 + 3 ^ 40 * 6408126 * 2
def baseEnd_6408126 : Nat := 3290448732573500411254571

theorem tailTrace_6408126 : CollatzResearch.WordTrace tailWord_6408126 prefixEnd_6408126 3290448732573500411254571 := by
  unfold tailWord_6408126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215444547807674704327529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155815704254974265089746821 29215444547807674704327529)
  ·
    refine ⟨21911583410855756028245647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29215444547807674704327529 21911583410855756028245647)
    ·
      refine ⟨32867375116283634042368471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21911583410855756028245647 32867375116283634042368471)
      ·
        refine ⟨49301062674425451063552707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32867375116283634042368471 49301062674425451063552707)
        ·
          refine ⟨73951594011638176595329061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49301062674425451063552707 73951594011638176595329061)
          ·
            refine ⟨13865923877182158111624199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73951594011638176595329061 13865923877182158111624199)
            ·
              refine ⟨20798885815773237167436299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13865923877182158111624199 20798885815773237167436299)
              ·
                refine ⟨31198328723659855751154449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20798885815773237167436299 31198328723659855751154449)
                ·
                  refine ⟨23398746542744891813365837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31198328723659855751154449 23398746542744891813365837)
                  ·
                    refine ⟨8774529953529334430012189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23398746542744891813365837 8774529953529334430012189)
                    ·
                      refine ⟨3290448732573500411254571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8774529953529334430012189 3290448732573500411254571)
                      ·
                        rfl

theorem cell23_6408126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_6408126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408126 prefixEnd_6408126 := by exact prefixLift 6408126
  have htrace : WordTrace (prefixWord ++ tailWord_6408126) baseStart_6408126 baseEnd_6408126 := by
    simpa [prefixWord, tailWord_6408126, baseEnd_6408126] using wordTrace_append hprefix tailTrace_6408126
  have hstable : (prefixWord ++ tailWord_6408126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408126).length < 2 ^ (prefixWord ++ tailWord_6408126).sum := by decide
  have hdescent : baseEnd_6408126 < baseStart_6408126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408146 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_6408146 : Nat := 118140960795 + 6408146 * 2 ^ 59
def prefixEnd_6408146 : Nat := 4983230072969 + 3 ^ 40 * 6408146 * 2
def baseEnd_6408146 : Nat := 1096819667395530111001493

theorem tailTrace_6408146 : CollatzResearch.WordTrace tailWord_6408146 prefixEnd_6408146 1096819667395530111001493 := by
  unfold tailWord_6408146
  simp only [CollatzResearch.WordTrace]
  refine ⟨58431071460597235262587073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155816190561592627366898861 58431071460597235262587073)
  ·
    refine ⟨43823303595447926446940305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58431071460597235262587073 43823303595447926446940305)
    ·
      refine ⟨32867477696585944835205229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43823303595447926446940305 32867477696585944835205229)
      ·
        refine ⟨12325304136219729313201961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32867477696585944835205229 12325304136219729313201961)
        ·
          refine ⟨9243978102164796984901471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12325304136219729313201961 9243978102164796984901471)
          ·
            refine ⟨13865967153247195477352207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243978102164796984901471 13865967153247195477352207)
            ·
              refine ⟨20798950729870793216028311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13865967153247195477352207 20798950729870793216028311)
              ·
                refine ⟨31198426094806189824042467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20798950729870793216028311 31198426094806189824042467)
                ·
                  refine ⟨46797639142209284736063701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31198426094806189824042467 46797639142209284736063701)
                  ·
                    refine ⟨1096819667395530111001493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46797639142209284736063701 1096819667395530111001493)
                    ·
                      rfl

theorem cell23_6408146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_6408146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408146 prefixEnd_6408146 := by exact prefixLift 6408146
  have htrace : WordTrace (prefixWord ++ tailWord_6408146) baseStart_6408146 baseEnd_6408146 := by
    simpa [prefixWord, tailWord_6408146, baseEnd_6408146] using wordTrace_append hprefix tailTrace_6408146
  have hstable : (prefixWord ++ tailWord_6408146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408146).length < 2 ^ (prefixWord ++ tailWord_6408146).sum := by decide
  have hdescent : baseEnd_6408146 < baseStart_6408146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408150 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_6408150 : Nat := 118140960795 + 6408150 * 2 ^ 59
def prefixEnd_6408150 : Nat := 4983230072969 + 3 ^ 40 * 6408150 * 2
def baseEnd_6408150 : Nat := 365606784012134257483829

theorem tailTrace_6408150 : CollatzResearch.WordTrace tailWord_6408150 prefixEnd_6408150 365606784012134257483829 := by
  unfold tailWord_6408150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607776983398403108343369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155816287822916299822329269 14607776983398403108343369)
  ·
    refine ⟨10955832737548802331257527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14607776983398403108343369 10955832737548802331257527)
    ·
      refine ⟨16433749106323203496886291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10955832737548802331257527 16433749106323203496886291)
      ·
        refine ⟨24650623659484805245329437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16433749106323203496886291 24650623659484805245329437)
        ·
          refine ⟨9243983872306801966998539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24650623659484805245329437 9243983872306801966998539)
          ·
            refine ⟨13865975808460202950497809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243983872306801966998539 13865975808460202950497809)
            ·
              refine ⟨10399481856345152212873357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13865975808460202950497809 10399481856345152212873357)
              ·
                refine ⟨3899805696129432079827509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10399481856345152212873357 3899805696129432079827509)
                ·
                  refine ⟨365606784012134257483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3899805696129432079827509 365606784012134257483829)
                  ·
                    rfl

theorem cell23_6408150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_6408150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408150 prefixEnd_6408150 := by exact prefixLift 6408150
  have htrace : WordTrace (prefixWord ++ tailWord_6408150) baseStart_6408150 baseEnd_6408150 := by
    simpa [prefixWord, tailWord_6408150, baseEnd_6408150] using wordTrace_append hprefix tailTrace_6408150
  have hstable : (prefixWord ++ tailWord_6408150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408150).length < 2 ^ (prefixWord ++ tailWord_6408150).sum := by decide
  have hdescent : baseEnd_6408150 < baseStart_6408150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408189 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 6]
def baseStart_6408189 : Nat := 118140960795 + 6408189 * 2 ^ 59
def prefixEnd_6408189 : Nat := 4983230072969 + 3 ^ 40 * 6408189 * 2
def baseEnd_6408189 : Nat := 365609009094970407196309

theorem tailTrace_6408189 : CollatzResearch.WordTrace tailWord_6408189 prefixEnd_6408189 365609009094970407196309 := by
  unfold tailWord_6408189
  simp only [CollatzResearch.WordTrace]
  refine ⟨233725854181233159394163621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155817236120822106262775747 233725854181233159394163621)
  ·
    refine ⟨43823597658981217386405679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233725854181233159394163621 43823597658981217386405679)
    ·
      refine ⟨65735396488471826079608519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43823597658981217386405679 65735396488471826079608519)
      ·
        refine ⟨98603094732707739119412779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65735396488471826079608519 98603094732707739119412779)
        ·
          refine ⟨147904642099061608679119169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98603094732707739119412779 147904642099061608679119169)
          ·
            refine ⟨110928481574296206509339377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147904642099061608679119169 110928481574296206509339377)
            ·
              refine ⟨83196361180722154882004533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110928481574296206509339377 83196361180722154882004533)
              ·
                refine ⟨7799658860692702020187925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83196361180722154882004533 7799658860692702020187925)
                ·
                  refine ⟨365609009094970407196309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7799658860692702020187925 365609009094970407196309)
                  ·
                    rfl

theorem cell23_6408189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_6408189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408189 prefixEnd_6408189 := by exact prefixLift 6408189
  have htrace : WordTrace (prefixWord ++ tailWord_6408189) baseStart_6408189 baseEnd_6408189 := by
    simpa [prefixWord, tailWord_6408189, baseEnd_6408189] using wordTrace_append hprefix tailTrace_6408189
  have hstable : (prefixWord ++ tailWord_6408189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408189).length < 2 ^ (prefixWord ++ tailWord_6408189).sum := by decide
  have hdescent : baseEnd_6408189 < baseStart_6408189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408256 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_6408256 : Nat := 118140960795 + 6408256 * 2 ^ 59
def prefixEnd_6408256 : Nat := 4983230072969 + 3 ^ 40 * 6408256 * 2
def baseEnd_6408256 : Nat := 3290515485058584902628973

theorem tailTrace_6408256 : CollatzResearch.WordTrace tailWord_6408256 prefixEnd_6408256 3290515485058584902628973 := by
  unfold tailWord_6408256
  simp only [CollatzResearch.WordTrace]
  refine ⟨116864148935995214918426311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155818865247993619891235081 116864148935995214918426311)
  ·
    refine ⟨175296223403992822377639467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116864148935995214918426311 175296223403992822377639467)
    ·
      refine ⟨262944335105989233566459201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175296223403992822377639467 262944335105989233566459201)
      ·
        refine ⟨197208251329491925174844401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262944335105989233566459201 197208251329491925174844401)
        ·
          refine ⟨147906188497118943881133301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197208251329491925174844401 147906188497118943881133301)
          ·
            refine ⟨13866205171604900988856247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147906188497118943881133301 13866205171604900988856247)
            ·
              refine ⟨20799307757407351483284371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13866205171604900988856247 20799307757407351483284371)
              ·
                refine ⟨31198961636111027224926557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20799307757407351483284371 31198961636111027224926557)
                ·
                  refine ⟨11699610613541635209347459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31198961636111027224926557 11699610613541635209347459)
                  ·
                    refine ⟨17549415920312452814021189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11699610613541635209347459 17549415920312452814021189)
                    ·
                      refine ⟨3290515485058584902628973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17549415920312452814021189 3290515485058584902628973)
                      ·
                        rfl

theorem cell23_6408256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_6408256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408256 prefixEnd_6408256 := by exact prefixLift 6408256
  have htrace : WordTrace (prefixWord ++ tailWord_6408256) baseStart_6408256 baseEnd_6408256 := by
    simpa [prefixWord, tailWord_6408256, baseEnd_6408256] using wordTrace_append hprefix tailTrace_6408256
  have hstable : (prefixWord ++ tailWord_6408256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408256).length < 2 ^ (prefixWord ++ tailWord_6408256).sum := by decide
  have hdescent : baseEnd_6408256 < baseStart_6408256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408284 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_6408284 : Nat := 118140960795 + 6408284 * 2 ^ 59
def prefixEnd_6408284 : Nat := 4983230072969 + 3 ^ 40 * 6408284 * 2
def baseEnd_6408284 : Nat := 3290529862516910793078845

theorem tailTrace_6408284 : CollatzResearch.WordTrace tailWord_6408284 prefixEnd_6408284 3290529862516910793078845 := by
  unfold tailWord_6408284
  simp only [CollatzResearch.WordTrace]
  refine ⟨116864659557944495309435953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155819546077259327079247937 116864659557944495309435953)
  ·
    refine ⟨87648494668458371482076965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116864659557944495309435953 87648494668458371482076965)
    ·
      refine ⟨16434092750335944652889431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87648494668458371482076965 16434092750335944652889431)
      ·
        refine ⟨24651139125503916979334147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16434092750335944652889431 24651139125503916979334147)
        ·
          refine ⟨36976708688255875469001221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24651139125503916979334147 36976708688255875469001221)
          ·
            refine ⟨6933132879047976650437729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36976708688255875469001221 6933132879047976650437729)
            ·
              refine ⟨5199849659285982487828297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6933132879047976650437729 5199849659285982487828297)
              ·
                refine ⟨3899887244464486865871223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5199849659285982487828297 3899887244464486865871223)
                ·
                  refine ⟨5849830866696730298806835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899887244464486865871223 5849830866696730298806835)
                  ·
                    refine ⟨8774746300045095448210253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5849830866696730298806835 8774746300045095448210253)
                    ·
                      refine ⟨3290529862516910793078845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8774746300045095448210253 3290529862516910793078845)
                      ·
                        rfl

theorem cell23_6408284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_6408284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408284 prefixEnd_6408284 := by exact prefixLift 6408284
  have htrace : WordTrace (prefixWord ++ tailWord_6408284) baseStart_6408284 baseEnd_6408284 := by
    simpa [prefixWord, tailWord_6408284, baseEnd_6408284] using wordTrace_append hprefix tailTrace_6408284
  have hstable : (prefixWord ++ tailWord_6408284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408284).length < 2 ^ (prefixWord ++ tailWord_6408284).sum := by decide
  have hdescent : baseEnd_6408284 < baseStart_6408284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408416 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_6408416 : Nat := 118140960795 + 6408416 * 2 ^ 59
def prefixEnd_6408416 : Nat := 4983230072969 + 3 ^ 40 * 6408416 * 2
def baseEnd_6408416 : Nat := 1096865880654434758876079

theorem tailTrace_6408416 : CollatzResearch.WordTrace tailWord_6408416 prefixEnd_6408416 1096865880654434758876079 := by
  unfold tailWord_6408416
  simp only [CollatzResearch.WordTrace]
  refine ⟨116867066775705388581338551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155822755700940518108451401 116867066775705388581338551)
  ·
    refine ⟨175300600163558082872007827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116867066775705388581338551 175300600163558082872007827)
    ·
      refine ⟨262950900245337124308011741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175300600163558082872007827 262950900245337124308011741)
      ·
        refine ⟨98606587592001421615504403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262950900245337124308011741 98606587592001421615504403)
        ·
          refine ⟨147909881388002132423256605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98606587592001421615504403 147909881388002132423256605)
          ·
            refine ⟨55466205520500799658721227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147909881388002132423256605 55466205520500799658721227)
            ·
              refine ⟨83199308280751199488081841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55466205520500799658721227 83199308280751199488081841)
              ·
                refine ⟨62399481210563399616061381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83199308280751199488081841 62399481210563399616061381)
                ·
                  refine ⟨11699902726980637428011509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62399481210563399616061381 11699902726980637428011509)
                  ·
                    refine ⟨1096865880654434758876079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11699902726980637428011509 1096865880654434758876079)
                    ·
                      rfl

theorem cell23_6408416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_6408416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408416 prefixEnd_6408416 := by exact prefixLift 6408416
  have htrace : WordTrace (prefixWord ++ tailWord_6408416) baseStart_6408416 baseEnd_6408416 := by
    simpa [prefixWord, tailWord_6408416, baseEnd_6408416] using wordTrace_append hprefix tailTrace_6408416
  have hstable : (prefixWord ++ tailWord_6408416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408416).length < 2 ^ (prefixWord ++ tailWord_6408416).sum := by decide
  have hdescent : baseEnd_6408416 < baseStart_6408416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408418 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6408418 : Nat := 118140960795 + 6408418 * 2 ^ 59
def prefixEnd_6408418 : Nat := 4983230072969 + 3 ^ 40 * 6408418 * 2
def baseEnd_6408418 : Nat := 3290598668924613268803229

theorem tailTrace_6408418 : CollatzResearch.WordTrace tailWord_6408418 prefixEnd_6408418 3290598668924613268803229 := by
  unfold tailWord_6408418
  simp only [CollatzResearch.WordTrace]
  refine ⟨58433551624350882876062477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155822804331602354336166605 58433551624350882876062477)
  ·
    refine ⟨21912581859131581078523429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58433551624350882876062477 21912581859131581078523429)
    ·
      refine ⟨4108609098587171452223143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21912581859131581078523429 4108609098587171452223143)
      ·
        refine ⟨6162913647880757178334715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108609098587171452223143 6162913647880757178334715)
        ·
          refine ⟨9244370471821135767502073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162913647880757178334715 9244370471821135767502073)
          ·
            refine ⟨6933277853865851825626555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9244370471821135767502073 6933277853865851825626555)
            ·
              refine ⟨10399916780798777738439833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933277853865851825626555 10399916780798777738439833)
              ·
                refine ⟨7799937585599083303829875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10399916780798777738439833 7799937585599083303829875)
                ·
                  refine ⟨11699906378398624955744813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7799937585599083303829875 11699906378398624955744813)
                  ·
                    refine ⟨4387464891899484358404305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11699906378398624955744813 4387464891899484358404305)
                    ·
                      refine ⟨3290598668924613268803229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387464891899484358404305 3290598668924613268803229)
                      ·
                        rfl

theorem cell23_6408418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6408418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408418 prefixEnd_6408418 := by exact prefixLift 6408418
  have htrace : WordTrace (prefixWord ++ tailWord_6408418) baseStart_6408418 baseEnd_6408418 := by
    simpa [prefixWord, tailWord_6408418, baseEnd_6408418] using wordTrace_append hprefix tailTrace_6408418
  have hstable : (prefixWord ++ tailWord_6408418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408418).length < 2 ^ (prefixWord ++ tailWord_6408418).sum := by decide
  have hdescent : baseEnd_6408418 < baseStart_6408418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408426 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_6408426 : Nat := 118140960795 + 6408426 * 2 ^ 59
def prefixEnd_6408426 : Nat := 4983230072969 + 3 ^ 40 * 6408426 * 2
def baseEnd_6408426 : Nat := 3290602776769849237503191

theorem tailTrace_6408426 : CollatzResearch.WordTrace tailWord_6408426 prefixEnd_6408426 3290602776769849237503191 := by
  unfold tailWord_6408426
  simp only [CollatzResearch.WordTrace]
  refine ⟨58433624570343637217635283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155822998854249699247027421 58433624570343637217635283)
  ·
    refine ⟨87650436855515455826452925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58433624570343637217635283 87650436855515455826452925)
    ·
      refine ⟨32868913820818295934919847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87650436855515455826452925 32868913820818295934919847)
      ·
        refine ⟨49303370731227443902379771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32868913820818295934919847 49303370731227443902379771)
        ·
          refine ⟨73955056096841165853569657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49303370731227443902379771 73955056096841165853569657)
          ·
            refine ⟨55466292072630874390177243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73955056096841165853569657 55466292072630874390177243)
            ·
              refine ⟨83199438108946311585265865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55466292072630874390177243 83199438108946311585265865)
              ·
                refine ⟨62399578581709733688949399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83199438108946311585265865 62399578581709733688949399)
                ·
                  refine ⟨93599367872564600533424099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62399578581709733688949399 93599367872564600533424099)
                  ·
                    refine ⟨140399051808846900800136149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93599367872564600533424099 140399051808846900800136149)
                    ·
                      refine ⟨3290602776769849237503191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140399051808846900800136149 3290602776769849237503191)
                      ·
                        rfl

theorem cell23_6408426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_6408426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408426 prefixEnd_6408426 := by exact prefixLift 6408426
  have htrace : WordTrace (prefixWord ++ tailWord_6408426) baseStart_6408426 baseEnd_6408426 := by
    simpa [prefixWord, tailWord_6408426, baseEnd_6408426] using wordTrace_append hprefix tailTrace_6408426
  have hstable : (prefixWord ++ tailWord_6408426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408426).length < 2 ^ (prefixWord ++ tailWord_6408426).sum := by decide
  have hdescent : baseEnd_6408426 < baseStart_6408426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408450 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_6408450 : Nat := 118140960795 + 6408450 * 2 ^ 59
def prefixEnd_6408450 : Nat := 4983230072969 + 3 ^ 40 * 6408450 * 2
def baseEnd_6408450 : Nat := 1096871700101852381201027

theorem tailTrace_6408450 : CollatzResearch.WordTrace tailWord_6408450 prefixEnd_6408450 1096871700101852381201027 := by
  unfold tailWord_6408450
  simp only [CollatzResearch.WordTrace]
  refine ⟨58433843408321900242353701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155823582422191733979609869 58433843408321900242353701)
  ·
    refine ⟨10956345639060356295441319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58433843408321900242353701 10956345639060356295441319)
    ·
      refine ⟨16434518458590534443161979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10956345639060356295441319 16434518458590534443161979)
      ·
        refine ⟨24651777687885801664742969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16434518458590534443161979 24651777687885801664742969)
        ·
          refine ⟨18488833265914351248557227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24651777687885801664742969 18488833265914351248557227)
          ·
            refine ⟨27733249898871526872835841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18488833265914351248557227 27733249898871526872835841)
            ·
              refine ⟨20799937424153645154626881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27733249898871526872835841 20799937424153645154626881)
              ·
                refine ⟨15599953068115233865970161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20799937424153645154626881 15599953068115233865970161)
                ·
                  refine ⟨11699964801086425399477621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15599953068115233865970161 11699964801086425399477621)
                  ·
                    refine ⟨1096871700101852381201027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11699964801086425399477621 1096871700101852381201027)
                    ·
                      rfl

theorem cell23_6408450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_6408450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408450 prefixEnd_6408450 := by exact prefixLift 6408450
  have htrace : WordTrace (prefixWord ++ tailWord_6408450) baseStart_6408450 baseEnd_6408450 := by
    simpa [prefixWord, tailWord_6408450, baseEnd_6408450] using wordTrace_append hprefix tailTrace_6408450
  have hstable : (prefixWord ++ tailWord_6408450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408450).length < 2 ^ (prefixWord ++ tailWord_6408450).sum := by decide
  have hdescent : baseEnd_6408450 < baseStart_6408450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408476 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 10]
def baseStart_6408476 : Nat := 118140960795 + 6408476 * 2 ^ 59
def prefixEnd_6408476 : Nat := 4983230072969 + 3 ^ 40 * 6408476 * 2
def baseEnd_6408476 : Nat := 365625383422508226875329

theorem tailTrace_6408476 : CollatzResearch.WordTrace tailWord_6408476 prefixEnd_6408476 365625383422508226875329 := by
  unfold tailWord_6408476
  simp only [CollatzResearch.WordTrace]
  refine ⟨116868160965596703704930641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155824214620795604939907521 116868160965596703704930641)
  ·
    refine ⟨87651120724197527778697981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116868160965596703704930641 87651120724197527778697981)
    ·
      refine ⟨32869170271574072917011743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87651120724197527778697981 32869170271574072917011743)
      ·
        refine ⟨49303755407361109375517615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32869170271574072917011743 49303755407361109375517615)
        ·
          refine ⟨73955633111041664063276423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49303755407361109375517615 73955633111041664063276423)
          ·
            refine ⟨110933449666562496094914635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73955633111041664063276423 110933449666562496094914635)
            ·
              refine ⟨166400174499843744142371953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110933449666562496094914635 166400174499843744142371953)
              ·
                refine ⟨124800130874882808106778965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166400174499843744142371953 124800130874882808106778965)
                ·
                  refine ⟨365625383422508226875329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124800130874882808106778965 365625383422508226875329)
                  ·
                    rfl

theorem cell23_6408476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_6408476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408476 prefixEnd_6408476 := by exact prefixLift 6408476
  have htrace : WordTrace (prefixWord ++ tailWord_6408476) baseStart_6408476 baseEnd_6408476 := by
    simpa [prefixWord, tailWord_6408476, baseEnd_6408476] using wordTrace_append hprefix tailTrace_6408476
  have hstable : (prefixWord ++ tailWord_6408476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408476).length < 2 ^ (prefixWord ++ tailWord_6408476).sum := by decide
  have hdescent : baseEnd_6408476 < baseStart_6408476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408480 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 3, 4]
def baseStart_6408480 : Nat := 118140960795 + 6408480 * 2 ^ 59
def prefixEnd_6408480 : Nat := 4983230072969 + 3 ^ 40 * 6408480 * 2
def baseEnd_6408480 : Nat := 1096876834908397342075981

theorem tailTrace_6408480 : CollatzResearch.WordTrace tailWord_6408480 prefixEnd_6408480 1096876834908397342075981 := by
  unfold tailWord_6408480
  simp only [CollatzResearch.WordTrace]
  refine ⟨116868233911589458046503447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155824311882119277395337929 116868233911589458046503447)
  ·
    refine ⟨175302350867384187069755171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116868233911589458046503447 175302350867384187069755171)
    ·
      refine ⟨262953526301076280604632757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175302350867384187069755171 262953526301076280604632757)
      ·
        refine ⟨24651893090725901306684321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262953526301076280604632757 24651893090725901306684321)
        ·
          refine ⟨18488919818044425980013241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24651893090725901306684321 18488919818044425980013241)
          ·
            refine ⟨13866689863533319485009931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18488919818044425980013241 13866689863533319485009931)
            ·
              refine ⟨20800034795299979227514897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13866689863533319485009931 20800034795299979227514897)
              ·
                refine ⟨15600026096474984420636173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20800034795299979227514897 15600026096474984420636173)
                ·
                  refine ⟨5850009786178119157738565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15600026096474984420636173 5850009786178119157738565)
                  ·
                    refine ⟨1096876834908397342075981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850009786178119157738565 1096876834908397342075981)
                    ·
                      rfl

theorem cell23_6408480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_6408480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408480 prefixEnd_6408480 := by exact prefixLift 6408480
  have htrace : WordTrace (prefixWord ++ tailWord_6408480) baseStart_6408480 baseEnd_6408480 := by
    simpa [prefixWord, tailWord_6408480, baseEnd_6408480] using wordTrace_append hprefix tailTrace_6408480
  have hstable : (prefixWord ++ tailWord_6408480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408480).length < 2 ^ (prefixWord ++ tailWord_6408480).sum := by decide
  have hdescent : baseEnd_6408480 < baseStart_6408480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408510 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_6408510 : Nat := 118140960795 + 6408510 * 2 ^ 59
def prefixEnd_6408510 : Nat := 4983230072969 + 3 ^ 40 * 6408510 * 2
def baseEnd_6408510 : Nat := 365627323238314100983645

theorem tailTrace_6408510 : CollatzResearch.WordTrace tailWord_6408510 prefixEnd_6408510 365627323238314100983645 := by
  unfold tailWord_6408510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29217195251633778902074873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155825041342046820811065989 29217195251633778902074873)
  ·
    refine ⟨21912896438725334176556155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29217195251633778902074873 21912896438725334176556155)
    ·
      refine ⟨32869344658088001264834233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21912896438725334176556155 32869344658088001264834233)
      ·
        refine ⟨24652008493566000948625675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32869344658088001264834233 24652008493566000948625675)
        ·
          refine ⟨36978012740349001422938513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24652008493566000948625675 36978012740349001422938513)
          ·
            refine ⟨27733509555261751067203885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36978012740349001422938513 27733509555261751067203885)
            ·
              refine ⟨10400066083223156650201457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27733509555261751067203885 10400066083223156650201457)
              ·
                refine ⟨7800049562417367487651093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10400066083223156650201457 7800049562417367487651093)
                ·
                  refine ⟨365627323238314100983645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7800049562417367487651093 365627323238314100983645)
                  ·
                    rfl

theorem cell23_6408510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_6408510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408510 prefixEnd_6408510 := by exact prefixLift 6408510
  have htrace : WordTrace (prefixWord ++ tailWord_6408510) baseStart_6408510 baseEnd_6408510 := by
    simpa [prefixWord, tailWord_6408510, baseEnd_6408510] using wordTrace_append hprefix tailTrace_6408510
  have hstable : (prefixWord ++ tailWord_6408510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408510).length < 2 ^ (prefixWord ++ tailWord_6408510).sum := by decide
  have hdescent : baseEnd_6408510 < baseStart_6408510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408520 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_6408520 : Nat := 118140960795 + 6408520 * 2 ^ 59
def prefixEnd_6408520 : Nat := 4983230072969 + 3 ^ 40 * 6408520 * 2
def baseEnd_6408520 : Nat := 3290651043951371869727759

theorem tailTrace_6408520 : CollatzResearch.WordTrace tailWord_6408520 prefixEnd_6408520 3290651043951371869727759 := by
  unfold tailWord_6408520
  simp only [CollatzResearch.WordTrace]
  refine ⟨116868963371517001462231507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155825284495356001949642009 116868963371517001462231507)
  ·
    refine ⟨175303445057275502193347261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116868963371517001462231507 175303445057275502193347261)
    ·
      refine ⟨65738791896478313322505223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175303445057275502193347261 65738791896478313322505223)
      ·
        refine ⟨98608187844717469983757835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65738791896478313322505223 98608187844717469983757835)
        ·
          refine ⟨147912281767076204975636753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98608187844717469983757835 147912281767076204975636753)
          ·
            refine ⟨110934211325307153731727565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147912281767076204975636753 110934211325307153731727565)
            ·
              refine ⟨41600329246990182649397837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110934211325307153731727565 41600329246990182649397837)
              ·
                refine ⟨15600123467621318493524189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41600329246990182649397837 15600123467621318493524189)
                ·
                  refine ⟨5850046300357994435071571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15600123467621318493524189 5850046300357994435071571)
                  ·
                    refine ⟨8775069450536991652607357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850046300357994435071571 8775069450536991652607357)
                    ·
                      refine ⟨3290651043951371869727759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775069450536991652607357 3290651043951371869727759)
                      ·
                        rfl

theorem cell23_6408520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_6408520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408520 prefixEnd_6408520 := by exact prefixLift 6408520
  have htrace : WordTrace (prefixWord ++ tailWord_6408520) baseStart_6408520 baseEnd_6408520 := by
    simpa [prefixWord, tailWord_6408520, baseEnd_6408520] using wordTrace_append hprefix tailTrace_6408520
  have hstable : (prefixWord ++ tailWord_6408520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408520).length < 2 ^ (prefixWord ++ tailWord_6408520).sum := by decide
  have hdescent : baseEnd_6408520 < baseStart_6408520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408530 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_6408530 : Nat := 118140960795 + 6408530 * 2 ^ 59
def prefixEnd_6408530 : Nat := 4983230072969 + 3 ^ 40 * 6408530 * 2
def baseEnd_6408530 : Nat := 3290656178757916830602713

theorem tailTrace_6408530 : CollatzResearch.WordTrace tailWord_6408530 prefixEnd_6408530 3290656178757916830602713 := by
  unfold tailWord_6408530
  simp only [CollatzResearch.WordTrace]
  refine ⟨58434572868249443658081761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155825527648665183088218029 58434572868249443658081761)
  ·
    refine ⟨43825929651187082743561321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58434572868249443658081761 43825929651187082743561321)
    ·
      refine ⟨32869447238390312057670991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43825929651187082743561321 32869447238390312057670991)
      ·
        refine ⟨49304170857585468086506487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32869447238390312057670991 49304170857585468086506487)
        ·
          refine ⟨73956256286378202129759731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49304170857585468086506487 73956256286378202129759731)
          ·
            refine ⟨110934384429567303194639597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73956256286378202129759731 110934384429567303194639597)
            ·
              refine ⟨41600394161087738697989849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110934384429567303194639597 41600394161087738697989849)
              ·
                refine ⟨31200295620815804023492387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41600394161087738697989849 31200295620815804023492387)
                ·
                  refine ⟨46800443431223706035238581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31200295620815804023492387 46800443431223706035238581)
                  ·
                    refine ⟨4387541571677222440803617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46800443431223706035238581 4387541571677222440803617)
                    ·
                      refine ⟨3290656178757916830602713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387541571677222440803617 3290656178757916830602713)
                      ·
                        rfl

theorem cell23_6408530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_6408530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408530 prefixEnd_6408530 := by exact prefixLift 6408530
  have htrace : WordTrace (prefixWord ++ tailWord_6408530) baseStart_6408530 baseEnd_6408530 := by
    simpa [prefixWord, tailWord_6408530, baseEnd_6408530] using wordTrace_append hprefix tailTrace_6408530
  have hstable : (prefixWord ++ tailWord_6408530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408530).length < 2 ^ (prefixWord ++ tailWord_6408530).sum := by decide
  have hdescent : baseEnd_6408530 < baseStart_6408530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408543 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_6408543 : Nat := 118140960795 + 6408543 * 2 ^ 59
def prefixEnd_6408543 : Nat := 4983230072969 + 3 ^ 40 * 6408543 * 2
def baseEnd_6408543 : Nat := 3290662854006425279740153

theorem tailTrace_6408543 : CollatzResearch.WordTrace tailWord_6408543 prefixEnd_6408543 3290662854006425279740153 := by
  unfold tailWord_6408543
  simp only [CollatzResearch.WordTrace]
  refine ⟨233738765621950677852550283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155825843747967118568366855 233738765621950677852550283)
  ·
    refine ⟨350608148432926016778825425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233738765621950677852550283 350608148432926016778825425)
    ·
      refine ⟨262956111324694512584119069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350608148432926016778825425 262956111324694512584119069)
      ·
        refine ⟨98608541746760442219044651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262956111324694512584119069 98608541746760442219044651)
        ·
          refine ⟨147912812620140663328566977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98608541746760442219044651 147912812620140663328566977)
          ·
            refine ⟨110934609465105497496425233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147912812620140663328566977 110934609465105497496425233)
            ·
              refine ⟨83200957098829123122318925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110934609465105497496425233 83200957098829123122318925)
              ·
                refine ⟨31200358912060921170869597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83200957098829123122318925 31200358912060921170869597)
                ·
                  refine ⟨11700134592022845439076099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31200358912060921170869597 11700134592022845439076099)
                  ·
                    refine ⟨17550201888034268158614149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11700134592022845439076099 17550201888034268158614149)
                    ·
                      refine ⟨3290662854006425279740153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17550201888034268158614149 3290662854006425279740153)
                      ·
                        rfl

theorem cell23_6408543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_6408543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408543 prefixEnd_6408543 := by exact prefixLift 6408543
  have htrace : WordTrace (prefixWord ++ tailWord_6408543) baseStart_6408543 baseEnd_6408543 := by
    simpa [prefixWord, tailWord_6408543, baseEnd_6408543] using wordTrace_append hprefix tailTrace_6408543
  have hstable : (prefixWord ++ tailWord_6408543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408543).length < 2 ^ (prefixWord ++ tailWord_6408543).sum := by decide
  have hdescent : baseEnd_6408543 < baseStart_6408543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408553 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 6, 4]
def baseStart_6408553 : Nat := 118140960795 + 6408553 * 2 ^ 59
def prefixEnd_6408553 : Nat := 4983230072969 + 3 ^ 40 * 6408553 * 2
def baseEnd_6408553 : Nat := 1096889329604323413538369

theorem tailTrace_6408553 : CollatzResearch.WordTrace tailWord_6408553 prefixEnd_6408553 1096889329604323413538369 := by
  unfold tailWord_6408553
  simp only [CollatzResearch.WordTrace]
  refine ⟨233739130351914449560414313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155826086901276299706942875 233739130351914449560414313)
  ·
    refine ⟨175304347763935837170310735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233739130351914449560414313 175304347763935837170310735)
    ·
      refine ⟨262956521645903755755466103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175304347763935837170310735 262956521645903755755466103)
      ·
        refine ⟨394434782468855633633199155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262956521645903755755466103 394434782468855633633199155)
        ·
          refine ⟨591652173703283450449798733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394434782468855633633199155 591652173703283450449798733)
          ·
            refine ⟨221869565138731293918674525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591652173703283450449798733 221869565138731293918674525)
            ·
              refine ⟨83201086927024235219502947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221869565138731293918674525 83201086927024235219502947)
              ·
                refine ⟨124801630390536352829254421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83201086927024235219502947 124801630390536352829254421)
                ·
                  refine ⟨5850076424556391538871301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124801630390536352829254421 5850076424556391538871301)
                  ·
                    refine ⟨1096889329604323413538369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850076424556391538871301 1096889329604323413538369)
                    ·
                      rfl

theorem cell23_6408553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_6408553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408553 prefixEnd_6408553 := by exact prefixLift 6408553
  have htrace : WordTrace (prefixWord ++ tailWord_6408553) baseStart_6408553 baseEnd_6408553 := by
    simpa [prefixWord, tailWord_6408553, baseEnd_6408553] using wordTrace_append hprefix tailTrace_6408553
  have hstable : (prefixWord ++ tailWord_6408553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408553).length < 2 ^ (prefixWord ++ tailWord_6408553).sum := by decide
  have hdescent : baseEnd_6408553 < baseStart_6408553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408560 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4]
def baseStart_6408560 : Nat := 118140960795 + 6408560 * 2 ^ 59
def prefixEnd_6408560 : Nat := 4983230072969 + 3 ^ 40 * 6408560 * 2
def baseEnd_6408560 : Nat := 3290671583177551713227575

theorem tailTrace_6408560 : CollatzResearch.WordTrace tailWord_6408560 prefixEnd_6408560 3290671583177551713227575 := by
  unfold tailWord_6408560
  simp only [CollatzResearch.WordTrace]
  refine ⟨116869692831444544877959567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155826257108592726503946089 116869692831444544877959567)
  ·
    refine ⟨175304539247166817316939351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116869692831444544877959567 175304539247166817316939351)
    ·
      refine ⟨262956808870750225975409027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175304539247166817316939351 262956808870750225975409027)
      ·
        refine ⟨394435213306125338963113541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262956808870750225975409027 394435213306125338963113541)
        ·
          refine ⟨73956602494898501055583789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394435213306125338963113541 73956602494898501055583789)
          ·
            refine ⟨27733725935586937895843921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73956602494898501055583789 27733725935586937895843921)
            ·
              refine ⟨20800294451690203421882941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27733725935586937895843921 20800294451690203421882941)
              ·
                refine ⟨7800110419383826283206103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20800294451690203421882941 7800110419383826283206103)
                ·
                  refine ⟨11700165629075739424809155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7800110419383826283206103 11700165629075739424809155)
                  ·
                    refine ⟨17550248443613609137213733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11700165629075739424809155 17550248443613609137213733)
                    ·
                      refine ⟨3290671583177551713227575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17550248443613609137213733 3290671583177551713227575)
                      ·
                        rfl

theorem cell23_6408560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_6408560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408560 prefixEnd_6408560 := by exact prefixLift 6408560
  have htrace : WordTrace (prefixWord ++ tailWord_6408560) baseStart_6408560 baseEnd_6408560 := by
    simpa [prefixWord, tailWord_6408560, baseEnd_6408560] using wordTrace_append hprefix tailTrace_6408560
  have hstable : (prefixWord ++ tailWord_6408560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408560).length < 2 ^ (prefixWord ++ tailWord_6408560).sum := by decide
  have hdescent : baseEnd_6408560 < baseStart_6408560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408573 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_6408573 : Nat := 118140960795 + 6408573 * 2 ^ 59
def prefixEnd_6408573 : Nat := 4983230072969 + 3 ^ 40 * 6408573 * 2
def baseEnd_6408573 : Nat := 3290678258426060162365015

theorem tailTrace_6408573 : CollatzResearch.WordTrace tailWord_6408573 prefixEnd_6408573 3290678258426060162365015 := by
  unfold tailWord_6408573
  simp only [CollatzResearch.WordTrace]
  refine ⟨233739859811841992976142373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155826573207894661984094915 233739859811841992976142373)
  ·
    refine ⟨43826223714720373683026695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233739859811841992976142373 43826223714720373683026695)
    ·
      refine ⟨65739335572080560524540043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43826223714720373683026695 65739335572080560524540043)
      ·
        refine ⟨98609003358120840786810065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65739335572080560524540043 98609003358120840786810065)
        ·
          refine ⟨73956752518590630590107549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98609003358120840786810065 73956752518590630590107549)
          ·
            refine ⟨27733782194471486471290331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73956752518590630590107549 27733782194471486471290331)
            ·
              refine ⟨41600673291707229706935497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27733782194471486471290331 41600673291707229706935497)
              ·
                refine ⟨31200504968780422280201623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41600673291707229706935497 31200504968780422280201623)
                ·
                  refine ⟨46800757453170633420302435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31200504968780422280201623 46800757453170633420302435)
                  ·
                    refine ⟨70201136179755950130453653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46800757453170633420302435 70201136179755950130453653)
                    ·
                      refine ⟨3290678258426060162365015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70201136179755950130453653 3290678258426060162365015)
                      ·
                        rfl

theorem cell23_6408573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_6408573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408573 prefixEnd_6408573 := by exact prefixLift 6408573
  have htrace : WordTrace (prefixWord ++ tailWord_6408573) baseStart_6408573 baseEnd_6408573 := by
    simpa [prefixWord, tailWord_6408573, baseEnd_6408573] using wordTrace_append hprefix tailTrace_6408573
  have hstable : (prefixWord ++ tailWord_6408573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408573).length < 2 ^ (prefixWord ++ tailWord_6408573).sum := by decide
  have hdescent : baseEnd_6408573 < baseStart_6408573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408580 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_6408580 : Nat := 118140960795 + 6408580 * 2 ^ 59
def prefixEnd_6408580 : Nat := 4983230072969 + 3 ^ 40 * 6408580 * 2
def baseEnd_6408580 : Nat := 3290681852790641634977483

theorem tailTrace_6408580 : CollatzResearch.WordTrace tailWord_6408580 prefixEnd_6408580 3290681852790641634977483 := by
  unfold tailWord_6408580
  simp only [CollatzResearch.WordTrace]
  refine ⟨116870057561408316585823597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155826743415211088781098129 116870057561408316585823597)
  ·
    refine ⟨43826271585528118719683849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116870057561408316585823597 43826271585528118719683849)
    ·
      refine ⟨32869703689146089039762887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43826271585528118719683849 32869703689146089039762887)
      ·
        refine ⟨49304555533719133559644331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32869703689146089039762887 49304555533719133559644331)
        ·
          refine ⟨73956833300578700339466497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49304555533719133559644331 73956833300578700339466497)
          ·
            refine ⟨55467624975434025254599873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73956833300578700339466497 55467624975434025254599873)
            ·
              refine ⟨41600718731575518940949905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55467624975434025254599873 41600718731575518940949905)
              ·
                refine ⟨31200539048681639205712429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41600718731575518940949905 31200539048681639205712429)
                ·
                  refine ⟨11700202143255614702142161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31200539048681639205712429 11700202143255614702142161)
                  ·
                    refine ⟨8775151607441711026606621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11700202143255614702142161 8775151607441711026606621)
                    ·
                      refine ⟨3290681852790641634977483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775151607441711026606621 3290681852790641634977483)
                      ·
                        rfl

theorem cell23_6408580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_6408580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408580 prefixEnd_6408580 := by exact prefixLift 6408580
  have htrace : WordTrace (prefixWord ++ tailWord_6408580) baseStart_6408580 baseEnd_6408580 := by
    simpa [prefixWord, tailWord_6408580, baseEnd_6408580] using wordTrace_append hprefix tailTrace_6408580
  have hstable : (prefixWord ++ tailWord_6408580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408580).length < 2 ^ (prefixWord ++ tailWord_6408580).sum := by decide
  have hdescent : baseEnd_6408580 < baseStart_6408580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408583 : List Nat := [1, 1, 4, 2, 2, 1, 4, 8]
def baseStart_6408583 : Nat := 118140960795 + 6408583 * 2 ^ 59
def prefixEnd_6408583 : Nat := 4983230072969 + 3 ^ 40 * 6408583 * 2
def baseEnd_6408583 : Nat := 121877162712318708268147

theorem tailTrace_6408583 : CollatzResearch.WordTrace tailWord_6408583 prefixEnd_6408583 121877162712318708268147 := by
  unfold tailWord_6408583
  simp only [CollatzResearch.WordTrace]
  refine ⟨233740224541805764684006403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155826816361203843122670935 233740224541805764684006403)
  ·
    refine ⟨350610336812708647026009605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233740224541805764684006403 350610336812708647026009605)
    ·
      refine ⟨65739438152382871317376801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350610336812708647026009605 65739438152382871317376801)
      ·
        refine ⟨49304578614287153488032601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65739438152382871317376801 49304578614287153488032601)
        ·
          refine ⟨36978433960715365116024451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49304578614287153488032601 36978433960715365116024451)
          ·
            refine ⟨55467650941073047674036677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36978433960715365116024451 55467650941073047674036677)
            ·
              refine ⟨10400184551451196438881877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55467650941073047674036677 10400184551451196438881877)
              ·
                refine ⟨121877162712318708268147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10400184551451196438881877 121877162712318708268147)
                ·
                  rfl

theorem cell23_6408583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 8].length) (baseStart_6408583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408583 prefixEnd_6408583 := by exact prefixLift 6408583
  have htrace : WordTrace (prefixWord ++ tailWord_6408583) baseStart_6408583 baseEnd_6408583 := by
    simpa [prefixWord, tailWord_6408583, baseEnd_6408583] using wordTrace_append hprefix tailTrace_6408583
  have hstable : (prefixWord ++ tailWord_6408583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408583).length < 2 ^ (prefixWord ++ tailWord_6408583).sum := by decide
  have hdescent : baseEnd_6408583 < baseStart_6408583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408587 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 2, 4]
def baseStart_6408587 : Nat := 118140960795 + 6408587 * 2 ^ 59
def prefixEnd_6408587 : Nat := 4983230072969 + 3 ^ 40 * 6408587 * 2
def baseEnd_6408587 : Nat := 1096895149051741035863317

theorem tailTrace_6408587 : CollatzResearch.WordTrace tailWord_6408587 prefixEnd_6408587 1096895149051741035863317 := by
  unfold tailWord_6408587
  simp only [CollatzResearch.WordTrace]
  refine ⟨233740370433791273367152015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155826913622527515578101343 233740370433791273367152015)
  ·
    refine ⟨350610555650686910050728023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233740370433791273367152015 350610555650686910050728023)
    ·
      refine ⟨525915833476030365076092035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350610555650686910050728023 525915833476030365076092035)
      ·
        refine ⟨788873750214045547614138053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525915833476030365076092035 788873750214045547614138053)
        ·
          refine ⟨147913828165133540177650885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 788873750214045547614138053 147913828165133540177650885)
          ·
            refine ⟨27733842780962538783309541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147913828165133540177650885 27733842780962538783309541)
            ·
              refine ⟨5200095521430476021870539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27733842780962538783309541 5200095521430476021870539)
              ·
                refine ⟨7800143282145714032805809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5200095521430476021870539 7800143282145714032805809)
                ·
                  refine ⟨5850107461609285524604357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800143282145714032805809 5850107461609285524604357)
                  ·
                    refine ⟨1096895149051741035863317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850107461609285524604357 1096895149051741035863317)
                    ·
                      rfl

theorem cell23_6408587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 4].length) (baseStart_6408587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408587 prefixEnd_6408587 := by exact prefixLift 6408587
  have htrace : WordTrace (prefixWord ++ tailWord_6408587) baseStart_6408587 baseEnd_6408587 := by
    simpa [prefixWord, tailWord_6408587, baseEnd_6408587] using wordTrace_append hprefix tailTrace_6408587
  have hstable : (prefixWord ++ tailWord_6408587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408587).length < 2 ^ (prefixWord ++ tailWord_6408587).sum := by decide
  have hdescent : baseEnd_6408587 < baseStart_6408587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408590 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6408590 : Nat := 118140960795 + 6408590 * 2 ^ 59
def prefixEnd_6408590 : Nat := 4983230072969 + 3 ^ 40 * 6408590 * 2
def baseEnd_6408590 : Nat := 3290686987597186595852437

theorem tailTrace_6408590 : CollatzResearch.WordTrace tailWord_6408590 prefixEnd_6408590 3290686987597186595852437 := by
  unfold tailWord_6408590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29217559981597550609938903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155826986568520269919674149 29217559981597550609938903)
  ·
    refine ⟨43826339972396325914908355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29217559981597550609938903 43826339972396325914908355)
    ·
      refine ⟨65739509958594488872362533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43826339972396325914908355 65739509958594488872362533)
      ·
        refine ⟨12326158117236466663567975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65739509958594488872362533 12326158117236466663567975)
        ·
          refine ⟨18489237175854699995351963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12326158117236466663567975 18489237175854699995351963)
          ·
            refine ⟨27733855763782049993027945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489237175854699995351963 27733855763782049993027945)
            ·
              refine ⟨20800391822836537494770959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27733855763782049993027945 20800391822836537494770959)
              ·
                refine ⟨31200587734254806242156439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20800391822836537494770959 31200587734254806242156439)
                ·
                  refine ⟨46800881601382209363234659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31200587734254806242156439 46800881601382209363234659)
                  ·
                    refine ⟨70201322402073314044851989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46800881601382209363234659 70201322402073314044851989)
                    ·
                      refine ⟨3290686987597186595852437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70201322402073314044851989 3290686987597186595852437)
                      ·
                        rfl

theorem cell23_6408590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6408590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408590 prefixEnd_6408590 := by exact prefixLift 6408590
  have htrace : WordTrace (prefixWord ++ tailWord_6408590) baseStart_6408590 baseEnd_6408590 := by
    simpa [prefixWord, tailWord_6408590, baseEnd_6408590] using wordTrace_append hprefix tailTrace_6408590
  have hstable : (prefixWord ++ tailWord_6408590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408590).length < 2 ^ (prefixWord ++ tailWord_6408590).sum := by decide
  have hdescent : baseEnd_6408590 < baseStart_6408590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408637 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_6408637 : Nat := 118140960795 + 6408637 * 2 ^ 59
def prefixEnd_6408637 : Nat := 4983230072969 + 3 ^ 40 * 6408637 * 2
def baseEnd_6408637 : Nat := 3290711121187947911964721

theorem tailTrace_6408637 : CollatzResearch.WordTrace tailWord_6408637 prefixEnd_6408637 3290711121187947911964721 := by
  unfold tailWord_6408637
  simp only [CollatzResearch.WordTrace]
  refine ⟨233742194083610131906472165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155828129389073421270981443 233742194083610131906472165)
  ·
    refine ⟨43826661390676899732463531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233742194083610131906472165 43826661390676899732463531)
    ·
      refine ⟨65739992086015349598695297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43826661390676899732463531 65739992086015349598695297)
      ·
        refine ⟨49304994064511512199021473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65739992086015349598695297 49304994064511512199021473)
        ·
          refine ⟨36978745548383634149266105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49304994064511512199021473 36978745548383634149266105)
          ·
            refine ⟨27734059161287725611949579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36978745548383634149266105 27734059161287725611949579)
            ·
              refine ⟨41601088741931588417924369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27734059161287725611949579 41601088741931588417924369)
              ·
                refine ⟨31200816556448691313443277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41601088741931588417924369 31200816556448691313443277)
                ·
                  refine ⟨11700306208668259242541229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31200816556448691313443277 11700306208668259242541229)
                  ·
                    refine ⟨4387614828250597215952961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11700306208668259242541229 4387614828250597215952961)
                    ·
                      refine ⟨3290711121187947911964721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387614828250597215952961 3290711121187947911964721)
                      ·
                        rfl

theorem cell23_6408637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_6408637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408637 prefixEnd_6408637 := by exact prefixLift 6408637
  have htrace : WordTrace (prefixWord ++ tailWord_6408637) baseStart_6408637 baseEnd_6408637 := by
    simpa [prefixWord, tailWord_6408637, baseEnd_6408637] using wordTrace_append hprefix tailTrace_6408637
  have hstable : (prefixWord ++ tailWord_6408637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408637).length < 2 ^ (prefixWord ++ tailWord_6408637).sum := by decide
  have hdescent : baseEnd_6408637 < baseStart_6408637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408641 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6408641 : Nat := 118140960795 + 6408641 * 2 ^ 59
def prefixEnd_6408641 : Nat := 4983230072969 + 3 ^ 40 * 6408641 * 2
def baseEnd_6408641 : Nat := 3290713175110565896314703

theorem tailTrace_6408641 : CollatzResearch.WordTrace tailWord_6408641 prefixEnd_6408641 3290713175110565896314703 := by
  unfold tailWord_6408641
  simp only [CollatzResearch.WordTrace]
  refine ⟨233742339975595640589617777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155828226650397093726411851 233742339975595640589617777)
  ·
    refine ⟨175306754981696730442213333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233742339975595640589617777 175306754981696730442213333)
    ·
      refine ⟨4108752069883517119739375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 175306754981696730442213333 4108752069883517119739375)
      ·
        refine ⟨6163128104825275679609063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108752069883517119739375 6163128104825275679609063)
        ·
          refine ⟨9244692157237913519413595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163128104825275679609063 9244692157237913519413595)
          ·
            refine ⟨13867038235856870279120393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244692157237913519413595 13867038235856870279120393)
            ·
              refine ⟨10400278676892652709340295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13867038235856870279120393 10400278676892652709340295)
              ·
                refine ⟨15600418015338979064010443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400278676892652709340295 15600418015338979064010443)
                ·
                  refine ⟨23400627023008468596015665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15600418015338979064010443 23400627023008468596015665)
                  ·
                    refine ⟨17550470267256351447011749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23400627023008468596015665 17550470267256351447011749)
                    ·
                      refine ⟨3290713175110565896314703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17550470267256351447011749 3290713175110565896314703)
                      ·
                        rfl

theorem cell23_6408641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6408641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408641 prefixEnd_6408641 := by exact prefixLift 6408641
  have htrace : WordTrace (prefixWord ++ tailWord_6408641) baseStart_6408641 baseEnd_6408641 := by
    simpa [prefixWord, tailWord_6408641, baseEnd_6408641] using wordTrace_append hprefix tailTrace_6408641
  have hstable : (prefixWord ++ tailWord_6408641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408641).length < 2 ^ (prefixWord ++ tailWord_6408641).sum := by decide
  have hdescent : baseEnd_6408641 < baseStart_6408641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408644 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_6408644 : Nat := 118140960795 + 6408644 * 2 ^ 59
def prefixEnd_6408644 : Nat := 4983230072969 + 3 ^ 40 * 6408644 * 2
def baseEnd_6408644 : Nat := 3290714715552529384577189

theorem tailTrace_6408644 : CollatzResearch.WordTrace tailWord_6408644 prefixEnd_6408644 3290714715552529384577189 := by
  unfold tailWord_6408644
  simp only [CollatzResearch.WordTrace]
  refine ⟨116871224697292386050988493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155828299596389848067984657 116871224697292386050988493)
  ·
    refine ⟨43826709261484644769120685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116871224697292386050988493 43826709261484644769120685)
    ·
      refine ⟨16435015973056741788420257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43826709261484644769120685 16435015973056741788420257)
      ·
        refine ⟨12326261979792556341315193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16435015973056741788420257 12326261979792556341315193)
        ·
          refine ⟨9244696484844417255986395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12326261979792556341315193 9244696484844417255986395)
          ·
            refine ⟨13867044727266625883979593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244696484844417255986395 13867044727266625883979593)
            ·
              refine ⟨10400283545449969412984695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13867044727266625883979593 10400283545449969412984695)
              ·
                refine ⟨15600425318174954119477043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400283545449969412984695 15600425318174954119477043)
                ·
                  refine ⟨23400637977262431179215565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15600425318174954119477043 23400637977262431179215565)
                  ·
                    refine ⟨8775239241473411692205837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23400637977262431179215565 8775239241473411692205837)
                    ·
                      refine ⟨3290714715552529384577189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775239241473411692205837 3290714715552529384577189)
                      ·
                        rfl

theorem cell23_6408644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_6408644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408644 prefixEnd_6408644 := by exact prefixLift 6408644
  have htrace : WordTrace (prefixWord ++ tailWord_6408644) baseStart_6408644 baseEnd_6408644 := by
    simpa [prefixWord, tailWord_6408644, baseEnd_6408644] using wordTrace_append hprefix tailTrace_6408644
  have hstable : (prefixWord ++ tailWord_6408644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408644).length < 2 ^ (prefixWord ++ tailWord_6408644).sum := by decide
  have hdescent : baseEnd_6408644 < baseStart_6408644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408671 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 1, 3, 2]
def baseStart_6408671 : Nat := 118140960795 + 6408671 * 2 ^ 59
def prefixEnd_6408671 : Nat := 4983230072969 + 3 ^ 40 * 6408671 * 2
def baseEnd_6408671 : Nat := 3290728579530200778939565

theorem tailTrace_6408671 : CollatzResearch.WordTrace tailWord_6408671 prefixEnd_6408671 3290728579530200778939565 := by
  unfold tailWord_6408671
  simp only [CollatzResearch.WordTrace]
  refine ⟨233743434165486955713209867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155828956110324637142139911 233743434165486955713209867)
  ·
    refine ⟨350615151248230433569814801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233743434165486955713209867 350615151248230433569814801)
    ·
      refine ⟨262961363436172825177361101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350615151248230433569814801 262961363436172825177361101)
      ·
        refine ⟨98610511288564809441510413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262961363436172825177361101 98610511288564809441510413)
        ·
          refine ⟨36978941733211803540566405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98610511288564809441510413 36978941733211803540566405)
          ·
            refine ⟨6933551574977213163856201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36978941733211803540566405 6933551574977213163856201)
            ·
              refine ⟨5200163681232909872892151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6933551574977213163856201 5200163681232909872892151)
              ·
                refine ⟨7800245521849364809338227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5200163681232909872892151 7800245521849364809338227)
                ·
                  refine ⟨11700368282774047214007341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7800245521849364809338227 11700368282774047214007341)
                  ·
                    refine ⟨4387638106040267705252753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11700368282774047214007341 4387638106040267705252753)
                    ·
                      refine ⟨3290728579530200778939565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387638106040267705252753 3290728579530200778939565)
                      ·
                        rfl

theorem cell23_6408671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_6408671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408671 prefixEnd_6408671 := by exact prefixLift 6408671
  have htrace : WordTrace (prefixWord ++ tailWord_6408671) baseStart_6408671 baseEnd_6408671 := by
    simpa [prefixWord, tailWord_6408671, baseEnd_6408671] using wordTrace_append hprefix tailTrace_6408671
  have hstable : (prefixWord ++ tailWord_6408671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408671).length < 2 ^ (prefixWord ++ tailWord_6408671).sum := by decide
  have hdescent : baseEnd_6408671 < baseStart_6408671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408673 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 9]
def baseStart_6408673 : Nat := 118140960795 + 6408673 * 2 ^ 59
def prefixEnd_6408673 : Nat := 4983230072969 + 3 ^ 40 * 6408673 * 2
def baseEnd_6408673 : Nat := 365636622943501085679395

theorem tailTrace_6408673 : CollatzResearch.WordTrace tailWord_6408673 prefixEnd_6408673 365636622943501085679395 := by
  unfold tailWord_6408673
  simp only [CollatzResearch.WordTrace]
  refine ⟨233743507111479710054782673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155829004740986473369855115 233743507111479710054782673)
  ·
    refine ⟨175307630333609782541087005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233743507111479710054782673 175307630333609782541087005)
    ·
      refine ⟨65740361375103668452907627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175307630333609782541087005 65740361375103668452907627)
      ·
        refine ⟨98610542062655502679361441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65740361375103668452907627 98610542062655502679361441)
        ·
          refine ⟨73957906546991627009521081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98610542062655502679361441 73957906546991627009521081)
          ·
            refine ⟨55468429910243720257140811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73957906546991627009521081 55468429910243720257140811)
            ·
              refine ⟨83202644865365580385711217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55468429910243720257140811 83202644865365580385711217)
              ·
                refine ⟨62401983649024185289283413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83202644865365580385711217 62401983649024185289283413)
                ·
                  refine ⟨365636622943501085679395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62401983649024185289283413 365636622943501085679395)
                  ·
                    rfl

theorem cell23_6408673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_6408673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408673 prefixEnd_6408673 := by exact prefixLift 6408673
  have htrace : WordTrace (prefixWord ++ tailWord_6408673) baseStart_6408673 baseEnd_6408673 := by
    simpa [prefixWord, tailWord_6408673, baseEnd_6408673] using wordTrace_append hprefix tailTrace_6408673
  have hstable : (prefixWord ++ tailWord_6408673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408673).length < 2 ^ (prefixWord ++ tailWord_6408673).sum := by decide
  have hdescent : baseEnd_6408673 < baseStart_6408673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408680 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6408680 : Nat := 118140960795 + 6408680 * 2 ^ 59
def prefixEnd_6408680 : Nat := 4983230072969 + 3 ^ 40 * 6408680 * 2
def baseEnd_6408680 : Nat := 3290733200856091243727023

theorem tailTrace_6408680 : CollatzResearch.WordTrace tailWord_6408680 prefixEnd_6408680 3290733200856091243727023 := by
  unfold tailWord_6408680
  simp only [CollatzResearch.WordTrace]
  refine ⟨116871881211227175125143747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155829174948302900166858329 116871881211227175125143747)
  ·
    refine ⟨175307821816840762687715621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116871881211227175125143747 175307821816840762687715621)
    ·
      refine ⟨32870216590657643003946679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175307821816840762687715621 32870216590657643003946679)
      ·
        refine ⟨49305324885986464505920019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32870216590657643003946679 49305324885986464505920019)
        ·
          refine ⟨73957987328979696758880029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49305324885986464505920019 73957987328979696758880029)
          ·
            refine ⟨27734245248367386284580011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73957987328979696758880029 27734245248367386284580011)
            ·
              refine ⟨41601367872551079426870017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27734245248367386284580011 41601367872551079426870017)
              ·
                refine ⟨31201025904413309570152513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41601367872551079426870017 31201025904413309570152513)
                ·
                  refine ⟨23400769428309982177614385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31201025904413309570152513 23400769428309982177614385)
                  ·
                    refine ⟨17550577071232486633210789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23400769428309982177614385 17550577071232486633210789)
                    ·
                      refine ⟨3290733200856091243727023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17550577071232486633210789 3290733200856091243727023)
                      ·
                        rfl

theorem cell23_6408680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6408680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408680 prefixEnd_6408680 := by exact prefixLift 6408680
  have htrace : WordTrace (prefixWord ++ tailWord_6408680) baseStart_6408680 baseEnd_6408680 := by
    simpa [prefixWord, tailWord_6408680, baseEnd_6408680] using wordTrace_append hprefix tailTrace_6408680
  have hstable : (prefixWord ++ tailWord_6408680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408680).length < 2 ^ (prefixWord ++ tailWord_6408680).sum := by decide
  have hdescent : baseEnd_6408680 < baseStart_6408680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408701 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_6408701 : Nat := 118140960795 + 6408701 * 2 ^ 59
def prefixEnd_6408701 : Nat := 4983230072969 + 3 ^ 40 * 6408701 * 2
def baseEnd_6408701 : Nat := 3290743983949835661564427

theorem tailTrace_6408701 : CollatzResearch.WordTrace tailWord_6408701 prefixEnd_6408701 3290743983949835661564427 := by
  unfold tailWord_6408701
  simp only [CollatzResearch.WordTrace]
  refine ⟨233744528355378270836801957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155829685570252180557867971 233744528355378270836801957)
  ·
    refine ⟨43827099066633425781900367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233744528355378270836801957 43827099066633425781900367)
    ·
      refine ⟨65740648599950138672850551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43827099066633425781900367 65740648599950138672850551)
      ·
        refine ⟨98610972899925208009275827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65740648599950138672850551 98610972899925208009275827)
        ·
          refine ⟨147916459349887812013913741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98610972899925208009275827 147916459349887812013913741)
          ·
            refine ⟨55468672256207929505217653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147916459349887812013913741 55468672256207929505217653)
            ·
              refine ⟨5200188024019493391114155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55468672256207929505217653 5200188024019493391114155)
              ·
                refine ⟨7800282036029240086671233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5200188024019493391114155 7800282036029240086671233)
                ·
                  refine ⟨5850211527021930065003425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800282036029240086671233 5850211527021930065003425)
                  ·
                    refine ⟨4387658645266447548752569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5850211527021930065003425 4387658645266447548752569)
                    ·
                      refine ⟨3290743983949835661564427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387658645266447548752569 3290743983949835661564427)
                      ·
                        rfl

theorem cell23_6408701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_6408701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408701 prefixEnd_6408701 := by exact prefixLift 6408701
  have htrace : WordTrace (prefixWord ++ tailWord_6408701) baseStart_6408701 baseEnd_6408701 := by
    simpa [prefixWord, tailWord_6408701, baseEnd_6408701] using wordTrace_append hprefix tailTrace_6408701
  have hstable : (prefixWord ++ tailWord_6408701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408701).length < 2 ^ (prefixWord ++ tailWord_6408701).sum := by decide
  have hdescent : baseEnd_6408701 < baseStart_6408701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408703 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 3, 7]
def baseStart_6408703 : Nat := 118140960795 + 6408703 * 2 ^ 59
def prefixEnd_6408703 : Nat := 4983230072969 + 3 ^ 40 * 6408703 * 2
def baseEnd_6408703 : Nat := 1096915003637048217913139

theorem tailTrace_6408703 : CollatzResearch.WordTrace tailWord_6408703 prefixEnd_6408703 1096915003637048217913139 := by
  unfold tailWord_6408703
  simp only [CollatzResearch.WordTrace]
  refine ⟨233744601301371025178374763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155829734200914016785583175 233744601301371025178374763)
  ·
    refine ⟨350616901952056537767562145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233744601301371025178374763 350616901952056537767562145)
    ·
      refine ⟨262962676464042403325671609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350616901952056537767562145 262962676464042403325671609)
      ·
        refine ⟨197222007348031802494253707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262962676464042403325671609 197222007348031802494253707)
        ·
          refine ⟨295833011022047703741380561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197222007348031802494253707 295833011022047703741380561)
          ·
            refine ⟨221874758266535777806035421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295833011022047703741380561 221874758266535777806035421)
            ·
              refine ⟨83203034349950916677263283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221874758266535777806035421 83203034349950916677263283)
              ·
                refine ⟨124804551524926375015894925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83203034349950916677263283 124804551524926375015894925)
                ·
                  refine ⟨46801706821847390630960597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124804551524926375015894925 46801706821847390630960597)
                  ·
                    refine ⟨1096915003637048217913139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46801706821847390630960597 1096915003637048217913139)
                    ·
                      rfl

theorem cell23_6408703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_6408703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408703 prefixEnd_6408703 := by exact prefixLift 6408703
  have htrace : WordTrace (prefixWord ++ tailWord_6408703) baseStart_6408703 baseEnd_6408703 := by
    simpa [prefixWord, tailWord_6408703, baseEnd_6408703] using wordTrace_append hprefix tailTrace_6408703
  have hstable : (prefixWord ++ tailWord_6408703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408703).length < 2 ^ (prefixWord ++ tailWord_6408703).sum := by decide
  have hdescent : baseEnd_6408703 < baseStart_6408703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408713 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_6408713 : Nat := 118140960795 + 6408713 * 2 ^ 59
def prefixEnd_6408713 : Nat := 4983230072969 + 3 ^ 40 * 6408713 * 2
def baseEnd_6408713 : Nat := 3290750145717689614614371

theorem tailTrace_6408713 : CollatzResearch.WordTrace tailWord_6408713 prefixEnd_6408713 3290750145717689614614371 := by
  unfold tailWord_6408713
  simp only [CollatzResearch.WordTrace]
  refine ⟨233744966031334796886238793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155829977354223197924159195 233744966031334796886238793)
  ·
    refine ⟨175308724523501097664679095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233744966031334796886238793 175308724523501097664679095)
    ·
      refine ⟨262963086785251646497018643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175308724523501097664679095 262963086785251646497018643)
      ·
        refine ⟨394444630177877469745527965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262963086785251646497018643 394444630177877469745527965)
        ·
          refine ⟨147916736316704051154572987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394444630177877469745527965 147916736316704051154572987)
          ·
            refine ⟨221875104475056076731859481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147916736316704051154572987 221875104475056076731859481)
            ·
              refine ⟨166406328356292057548894611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221875104475056076731859481 166406328356292057548894611)
              ·
                refine ⟨249609492534438086323341917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166406328356292057548894611 249609492534438086323341917)
                ·
                  refine ⟨93603559700414282371253219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249609492534438086323341917 93603559700414282371253219)
                  ·
                    refine ⟨140405339550621423556879829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93603559700414282371253219 140405339550621423556879829)
                    ·
                      refine ⟨3290750145717689614614371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140405339550621423556879829 3290750145717689614614371)
                      ·
                        rfl

theorem cell23_6408713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_6408713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408713 prefixEnd_6408713 := by exact prefixLift 6408713
  have htrace : WordTrace (prefixWord ++ tailWord_6408713) baseStart_6408713 baseEnd_6408713 := by
    simpa [prefixWord, tailWord_6408713, baseEnd_6408713] using wordTrace_append hprefix tailTrace_6408713
  have hstable : (prefixWord ++ tailWord_6408713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408713).length < 2 ^ (prefixWord ++ tailWord_6408713).sum := by decide
  have hdescent : baseEnd_6408713 < baseStart_6408713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408757 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_6408757 : Nat := 118140960795 + 6408757 * 2 ^ 59
def prefixEnd_6408757 : Nat := 4983230072969 + 3 ^ 40 * 6408757 * 2
def baseEnd_6408757 : Nat := 3290772738866487442464169

theorem tailTrace_6408757 : CollatzResearch.WordTrace tailWord_6408757 prefixEnd_6408757 3290772738866487442464169 := by
  unfold tailWord_6408757
  simp only [CollatzResearch.WordTrace]
  refine ⟨233746570843175392400840525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155831047228783594933893683 233746570843175392400840525)
  ·
    refine ⟨87654964066190772150315197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233746570843175392400840525 87654964066190772150315197)
    ·
      refine ⟨32870611524821539556368199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87654964066190772150315197 32870611524821539556368199)
      ·
        refine ⟨49305917287232309334552299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32870611524821539556368199 49305917287232309334552299)
        ·
          refine ⟨73958875930848464001828449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49305917287232309334552299 73958875930848464001828449)
          ·
            refine ⟨55469156948136348001371337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73958875930848464001828449 55469156948136348001371337)
            ·
              refine ⟨41601867711102261001028503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55469156948136348001371337 41601867711102261001028503)
              ·
                refine ⟨62402801566653391501542755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41601867711102261001028503 62402801566653391501542755)
                ·
                  refine ⟨93604202349980087252314133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62402801566653391501542755 93604202349980087252314133)
                  ·
                    refine ⟨4387696985155316589952225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93604202349980087252314133 4387696985155316589952225)
                    ·
                      refine ⟨3290772738866487442464169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387696985155316589952225 3290772738866487442464169)
                      ·
                        rfl

theorem cell23_6408757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_6408757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408757 prefixEnd_6408757 := by exact prefixLift 6408757
  have htrace : WordTrace (prefixWord ++ tailWord_6408757) baseStart_6408757 baseEnd_6408757 := by
    simpa [prefixWord, tailWord_6408757, baseEnd_6408757] using wordTrace_append hprefix tailTrace_6408757
  have hstable : (prefixWord ++ tailWord_6408757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408757).length < 2 ^ (prefixWord ++ tailWord_6408757).sum := by decide
  have hdescent : baseEnd_6408757 < baseStart_6408757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408801 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 1, 4]
def baseStart_6408801 : Nat := 118140960795 + 6408801 * 2 ^ 59
def prefixEnd_6408801 : Nat := 4983230072969 + 3 ^ 40 * 6408801 * 2
def baseEnd_6408801 : Nat := 1096931777338428423437989

theorem tailTrace_6408801 : CollatzResearch.WordTrace tailWord_6408801 prefixEnd_6408801 1096931777338428423437989 := by
  unfold tailWord_6408801
  simp only [CollatzResearch.WordTrace]
  refine ⟨233748175655015987915442257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155832117103343991943628171 233748175655015987915442257)
  ·
    refine ⟨175311131741261990936581693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233748175655015987915442257 175311131741261990936581693)
    ·
      refine ⟨65741674402973246601218135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175311131741261990936581693 65741674402973246601218135)
      ·
        refine ⟨98612511604459869901827203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65741674402973246601218135 98612511604459869901827203)
        ·
          refine ⟨147918767406689804852740805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98612511604459869901827203 147918767406689804852740805)
          ·
            refine ⟨27734768888754338409888901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147918767406689804852740805 27734768888754338409888901)
            ·
              refine ⟨5200269166641438451854169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27734768888754338409888901 5200269166641438451854169)
              ·
                refine ⟨3900201874981078838890627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200269166641438451854169 3900201874981078838890627)
                ·
                  refine ⟨5850302812471618258335941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900201874981078838890627 5850302812471618258335941)
                  ·
                    refine ⟨1096931777338428423437989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850302812471618258335941 1096931777338428423437989)
                    ·
                      rfl

theorem cell23_6408801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_6408801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408801 prefixEnd_6408801 := by exact prefixLift 6408801
  have htrace : WordTrace (prefixWord ++ tailWord_6408801) baseStart_6408801 baseEnd_6408801 := by
    simpa [prefixWord, tailWord_6408801, baseEnd_6408801] using wordTrace_append hprefix tailTrace_6408801
  have hstable : (prefixWord ++ tailWord_6408801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408801).length < 2 ^ (prefixWord ++ tailWord_6408801).sum := by decide
  have hdescent : baseEnd_6408801 < baseStart_6408801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408847 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 4]
def baseStart_6408847 : Nat := 118140960795 + 6408847 * 2 ^ 59
def prefixEnd_6408847 : Nat := 4983230072969 + 3 ^ 40 * 6408847 * 2
def baseEnd_6408847 : Nat := 3290818952125392090338755

theorem tailTrace_6408847 : CollatzResearch.WordTrace tailWord_6408847 prefixEnd_6408847 3290818952125392090338755 := by
  unfold tailWord_6408847
  simp only [CollatzResearch.WordTrace]
  refine ⟨233749853412849337771616795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155833235608566225181077863 233749853412849337771616795)
  ·
    refine ⟨350624780119274006657425193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233749853412849337771616795 350624780119274006657425193)
    ·
      refine ⟨262968585089455504993068895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350624780119274006657425193 262968585089455504993068895)
      ·
        refine ⟨394452877634183257489603343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262968585089455504993068895 394452877634183257489603343)
        ·
          refine ⟨591679316451274886234405015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394452877634183257489603343 591679316451274886234405015)
          ·
            refine ⟨887518974676912329351607523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591679316451274886234405015 887518974676912329351607523)
            ·
              refine ⟨1331278462015368494027411285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887518974676912329351607523 1331278462015368494027411285)
              ·
                refine ⟨7800459738371299769691863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1331278462015368494027411285 7800459738371299769691863)
                ·
                  refine ⟨11700689607556949654537795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7800459738371299769691863 11700689607556949654537795)
                  ·
                    refine ⟨17551034411335424481806693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11700689607556949654537795 17551034411335424481806693)
                    ·
                      refine ⟨3290818952125392090338755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17551034411335424481806693 3290818952125392090338755)
                      ·
                        rfl

theorem cell23_6408847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_6408847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408847 prefixEnd_6408847 := by exact prefixLift 6408847
  have htrace : WordTrace (prefixWord ++ tailWord_6408847) baseStart_6408847 baseEnd_6408847 := by
    simpa [prefixWord, tailWord_6408847, baseEnd_6408847] using wordTrace_append hprefix tailTrace_6408847
  have hstable : (prefixWord ++ tailWord_6408847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408847).length < 2 ^ (prefixWord ++ tailWord_6408847).sum := by decide
  have hdescent : baseEnd_6408847 < baseStart_6408847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408857 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 4, 4]
def baseStart_6408857 : Nat := 118140960795 + 6408857 * 2 ^ 59
def prefixEnd_6408857 : Nat := 4983230072969 + 3 ^ 40 * 6408857 * 2
def baseEnd_6408857 : Nat := 1096941362310645683737903

theorem tailTrace_6408857 : CollatzResearch.WordTrace tailWord_6408857 prefixEnd_6408857 1096941362310645683737903 := by
  unfold tailWord_6408857
  simp only [CollatzResearch.WordTrace]
  refine ⟨233750218142813109479480825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155833478761875406319653883 233750218142813109479480825)
  ·
    refine ⟨175312663607109832109610619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233750218142813109479480825 175312663607109832109610619)
    ·
      refine ⟨262968995410664748164415929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175312663607109832109610619 262968995410664748164415929)
      ·
        refine ⟨197226746557998561123311947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262968995410664748164415929 197226746557998561123311947)
        ·
          refine ⟨295840119836997841684967921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197226746557998561123311947 295840119836997841684967921)
          ·
            refine ⟨221880089877748381263725941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295840119836997841684967921 221880089877748381263725941)
            ·
              refine ⟨20801258426038910743474307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221880089877748381263725941 20801258426038910743474307)
              ·
                refine ⟨31201887639058366115211461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20801258426038910743474307 31201887639058366115211461)
                ·
                  refine ⟨5850353932323443646602149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31201887639058366115211461 5850353932323443646602149)
                  ·
                    refine ⟨1096941362310645683737903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850353932323443646602149 1096941362310645683737903)
                    ·
                      rfl

theorem cell23_6408857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_6408857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408857 prefixEnd_6408857 := by exact prefixLift 6408857
  have htrace : WordTrace (prefixWord ++ tailWord_6408857) baseStart_6408857 baseEnd_6408857 := by
    simpa [prefixWord, tailWord_6408857, baseEnd_6408857] using wordTrace_append hprefix tailTrace_6408857
  have hstable : (prefixWord ++ tailWord_6408857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408857).length < 2 ^ (prefixWord ++ tailWord_6408857).sum := by decide
  have hdescent : baseEnd_6408857 < baseStart_6408857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408858 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6408858 : Nat := 118140960795 + 6408858 * 2 ^ 59
def prefixEnd_6408858 : Nat := 4983230072969 + 3 ^ 40 * 6408858 * 2
def baseEnd_6408858 : Nat := 3290824600412591547301205

theorem tailTrace_6408858 : CollatzResearch.WordTrace tailWord_6408858 prefixEnd_6408858 3290824600412591547301205 := by
  unfold tailWord_6408858
  simp only [CollatzResearch.WordTrace]
  refine ⟨58437563653952371662566807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155833503077206324433511485 58437563653952371662566807)
  ·
    refine ⟨87656345480928557493850211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58437563653952371662566807 87656345480928557493850211)
    ·
      refine ⟨131484518221392836240775317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87656345480928557493850211 131484518221392836240775317)
      ·
        refine ⟨6163336791627789198786343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131484518221392836240775317 6163336791627789198786343)
        ·
          refine ⟨9245005187441683798179515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163336791627789198786343 9245005187441683798179515)
          ·
            refine ⟨13867507781162525697269273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245005187441683798179515 13867507781162525697269273)
            ·
              refine ⟨10400630835871894272951955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13867507781162525697269273 10400630835871894272951955)
              ·
                refine ⟨15600946253807841409427933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400630835871894272951955 15600946253807841409427933)
                ·
                  refine ⟨5850354845177940528535475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15600946253807841409427933 5850354845177940528535475)
                  ·
                    refine ⟨8775532267766910792803213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850354845177940528535475 8775532267766910792803213)
                    ·
                      refine ⟨3290824600412591547301205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775532267766910792803213 3290824600412591547301205)
                      ·
                        rfl

theorem cell23_6408858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6408858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408858 prefixEnd_6408858 := by exact prefixLift 6408858
  have htrace : WordTrace (prefixWord ++ tailWord_6408858) baseStart_6408858 baseEnd_6408858 := by
    simpa [prefixWord, tailWord_6408858, baseEnd_6408858] using wordTrace_append hprefix tailTrace_6408858
  have hstable : (prefixWord ++ tailWord_6408858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408858).length < 2 ^ (prefixWord ++ tailWord_6408858).sum := by decide
  have hdescent : baseEnd_6408858 < baseStart_6408858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408867 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 3]
def baseStart_6408867 : Nat := 118140960795 + 6408867 * 2 ^ 59
def prefixEnd_6408867 : Nat := 4983230072969 + 3 ^ 40 * 6408867 * 2
def baseEnd_6408867 : Nat := 3290829221738482012088663

theorem tailTrace_6408867 : CollatzResearch.WordTrace tailWord_6408867 prefixEnd_6408867 3290829221738482012088663 := by
  unfold tailWord_6408867
  simp only [CollatzResearch.WordTrace]
  refine ⟨233750582872776881187344855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155833721915184587458229903 233750582872776881187344855)
  ·
    refine ⟨350625874309165321781017283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233750582872776881187344855 350625874309165321781017283)
    ·
      refine ⟨525938811463747982671525925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350625874309165321781017283 525938811463747982671525925)
      ·
        refine ⟨98613527149452746750911111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 525938811463747982671525925 98613527149452746750911111)
        ·
          refine ⟨147920290724179120126366667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98613527149452746750911111 147920290724179120126366667)
          ·
            refine ⟨221880436086268680189550001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147920290724179120126366667 221880436086268680189550001)
            ·
              refine ⟨166410327064701510142162501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221880436086268680189550001 166410327064701510142162501)
              ·
                refine ⟨31201936324631533151655469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166410327064701510142162501 31201936324631533151655469)
                ·
                  refine ⟨11700726121736824931870801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31201936324631533151655469 11700726121736824931870801)
                  ·
                    refine ⟨8775544591302618698903101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11700726121736824931870801 8775544591302618698903101)
                    ·
                      refine ⟨3290829221738482012088663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775544591302618698903101 3290829221738482012088663)
                      ·
                        rfl

theorem cell23_6408867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_6408867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408867 prefixEnd_6408867 := by exact prefixLift 6408867
  have htrace : WordTrace (prefixWord ++ tailWord_6408867) baseStart_6408867 baseEnd_6408867 := by
    simpa [prefixWord, tailWord_6408867, baseEnd_6408867] using wordTrace_append hprefix tailTrace_6408867
  have hstable : (prefixWord ++ tailWord_6408867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408867).length < 2 ^ (prefixWord ++ tailWord_6408867).sum := by decide
  have hdescent : baseEnd_6408867 < baseStart_6408867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408887 : List Nat := [1, 1, 3, 1, 6, 1, 1, 9]
def baseStart_6408887 : Nat := 118140960795 + 6408887 * 2 ^ 59
def prefixEnd_6408887 : Nat := 4983230072969 + 3 ^ 40 * 6408887 * 2
def baseEnd_6408887 : Nat := 121882944124132293845873

theorem tailTrace_6408887 : CollatzResearch.WordTrace tailWord_6408887 prefixEnd_6408887 121882944124132293845873 := by
  unfold tailWord_6408887
  simp only [CollatzResearch.WordTrace]
  refine ⟨233751312332704424603072915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155834208221802949735381943 233751312332704424603072915)
  ·
    refine ⟨350626968499056636904609373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233751312332704424603072915 350626968499056636904609373)
    ·
      refine ⟨131485113187146238839228515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350626968499056636904609373 131485113187146238839228515)
      ·
        refine ⟨197227669780719358258842773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131485113187146238839228515 197227669780719358258842773)
        ·
          refine ⟨9245047020971219918383255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197227669780719358258842773 9245047020971219918383255)
          ·
            refine ⟨13867570531456829877574883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245047020971219918383255 13867570531456829877574883)
            ·
              refine ⟨20801355797185244816362325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13867570531456829877574883 20801355797185244816362325)
              ·
                refine ⟨121882944124132293845873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20801355797185244816362325 121882944124132293845873)
                ·
                  rfl

theorem cell23_6408887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 9].length) (baseStart_6408887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408887 prefixEnd_6408887 := by exact prefixLift 6408887
  have htrace : WordTrace (prefixWord ++ tailWord_6408887) baseStart_6408887 baseEnd_6408887 := by
    simpa [prefixWord, tailWord_6408887, baseEnd_6408887] using wordTrace_append hprefix tailTrace_6408887
  have hstable : (prefixWord ++ tailWord_6408887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408887).length < 2 ^ (prefixWord ++ tailWord_6408887).sum := by decide
  have hdescent : baseEnd_6408887 < baseStart_6408887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408941 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6408941 : Nat := 118140960795 + 6408941 * 2 ^ 59
def prefixEnd_6408941 : Nat := 4983230072969 + 3 ^ 40 * 6408941 * 2
def baseEnd_6408941 : Nat := 3290867219306914722563323

theorem tailTrace_6408941 : CollatzResearch.WordTrace tailWord_6408941 prefixEnd_6408941 3290867219306914722563323 := by
  unfold tailWord_6408941
  simp only [CollatzResearch.WordTrace]
  refine ⟨233753281874508791825538677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155835521249672527883692451 233753281874508791825538677)
  ·
    refine ⟨21914370175735199233644251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233753281874508791825538677 21914370175735199233644251)
    ·
      refine ⟨32871555263602798850466377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21914370175735199233644251 32871555263602798850466377)
      ·
        refine ⟨24653666447702099137849783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32871555263602798850466377 24653666447702099137849783)
        ·
          refine ⟨36980499671553148706774675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24653666447702099137849783 36980499671553148706774675)
          ·
            refine ⟨55470749507329723060162013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36980499671553148706774675 55470749507329723060162013)
            ·
              refine ⟨20801531065248646147560755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55470749507329723060162013 20801531065248646147560755)
              ·
                refine ⟨31202296597872969221341133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20801531065248646147560755 31202296597872969221341133)
                ·
                  refine ⟨11700861224202363458002925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31202296597872969221341133 11700861224202363458002925)
                  ·
                    refine ⟨4387822959075886296751097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11700861224202363458002925 4387822959075886296751097)
                    ·
                      refine ⟨3290867219306914722563323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387822959075886296751097 3290867219306914722563323)
                      ·
                        rfl

theorem cell23_6408941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6408941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408941 prefixEnd_6408941 := by exact prefixLift 6408941
  have htrace : WordTrace (prefixWord ++ tailWord_6408941) baseStart_6408941 baseEnd_6408941 := by
    simpa [prefixWord, tailWord_6408941, baseEnd_6408941] using wordTrace_append hprefix tailTrace_6408941
  have hstable : (prefixWord ++ tailWord_6408941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408941).length < 2 ^ (prefixWord ++ tailWord_6408941).sum := by decide
  have hdescent : baseEnd_6408941 < baseStart_6408941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408954 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2]
def baseStart_6408954 : Nat := 118140960795 + 6408954 * 2 ^ 59
def prefixEnd_6408954 : Nat := 4983230072969 + 3 ^ 40 * 6408954 * 2
def baseEnd_6408954 : Nat := 3290873894555423171700763

theorem tailTrace_6408954 : CollatzResearch.WordTrace tailWord_6408954 prefixEnd_6408954 3290873894555423171700763 := by
  unfold tailWord_6408954
  simp only [CollatzResearch.WordTrace]
  refine ⟨58438439005865423761440479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155835837348974463363841277 58438439005865423761440479)
  ·
    refine ⟨87657658508798135642160719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58438439005865423761440479 87657658508798135642160719)
    ·
      refine ⟨131486487763197203463241079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87657658508798135642160719 131486487763197203463241079)
      ·
        refine ⟨197229731644795805194861619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131486487763197203463241079 197229731644795805194861619)
        ·
          refine ⟨295844597467193707792292429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197229731644795805194861619 295844597467193707792292429)
          ·
            refine ⟨110941724050197640422109661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295844597467193707792292429 110941724050197640422109661)
            ·
              refine ⟨41603146518824115158291123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110941724050197640422109661 41603146518824115158291123)
              ·
                refine ⟨62404719778236172737436685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41603146518824115158291123 62404719778236172737436685)
                ·
                  refine ⟨23401769916838564776538757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62404719778236172737436685 23401769916838564776538757)
                  ·
                    refine ⟨4387831859407230895601017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23401769916838564776538757 4387831859407230895601017)
                    ·
                      refine ⟨3290873894555423171700763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387831859407230895601017 3290873894555423171700763)
                      ·
                        rfl

theorem cell23_6408954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_6408954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408954 prefixEnd_6408954 := by exact prefixLift 6408954
  have htrace : WordTrace (prefixWord ++ tailWord_6408954) baseStart_6408954 baseEnd_6408954 := by
    simpa [prefixWord, tailWord_6408954, baseEnd_6408954] using wordTrace_append hprefix tailTrace_6408954
  have hstable : (prefixWord ++ tailWord_6408954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408954).length < 2 ^ (prefixWord ++ tailWord_6408954).sum := by decide
  have hdescent : baseEnd_6408954 < baseStart_6408954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408957 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_6408957 : Nat := 118140960795 + 6408957 * 2 ^ 59
def prefixEnd_6408957 : Nat := 4983230072969 + 3 ^ 40 * 6408957 * 2
def baseEnd_6408957 : Nat := 3290875434997386659963249

theorem tailTrace_6408957 : CollatzResearch.WordTrace tailWord_6408957 prefixEnd_6408957 3290875434997386659963249 := by
  unfold tailWord_6408957
  simp only [CollatzResearch.WordTrace]
  refine ⟨233753865442450826558121125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155835910294967217705414083 233753865442450826558121125)
  ·
    refine ⟨43828849770459529979647711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233753865442450826558121125 43828849770459529979647711)
    ·
      refine ⟨65743274655689294969471567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43828849770459529979647711 65743274655689294969471567)
      ·
        refine ⟨98614911983533942454207351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65743274655689294969471567 98614911983533942454207351)
        ·
          refine ⟨147922367975300913681311027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98614911983533942454207351 147922367975300913681311027)
          ·
            refine ⟨221883551962951370521966541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147922367975300913681311027 221883551962951370521966541)
            ·
              refine ⟨83206331986106763945737453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221883551962951370521966541 83206331986106763945737453)
              ·
                refine ⟨31202374494790036479651545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83206331986106763945737453 31202374494790036479651545)
                ·
                  refine ⟨23401780871092527359738659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31202374494790036479651545 23401780871092527359738659)
                  ·
                    refine ⟨35102671306638791039607989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23401780871092527359738659 35102671306638791039607989)
                    ·
                      refine ⟨3290875434997386659963249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35102671306638791039607989 3290875434997386659963249)
                      ·
                        rfl

theorem cell23_6408957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_6408957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408957 prefixEnd_6408957 := by exact prefixLift 6408957
  have htrace : WordTrace (prefixWord ++ tailWord_6408957) baseStart_6408957 baseEnd_6408957 := by
    simpa [prefixWord, tailWord_6408957, baseEnd_6408957] using wordTrace_append hprefix tailTrace_6408957
  have hstable : (prefixWord ++ tailWord_6408957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408957).length < 2 ^ (prefixWord ++ tailWord_6408957).sum := by decide
  have hdescent : baseEnd_6408957 < baseStart_6408957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408988 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_6408988 : Nat := 118140960795 + 6408988 * 2 ^ 59
def prefixEnd_6408988 : Nat := 4983230072969 + 3 ^ 40 * 6408988 * 2
def baseEnd_6408988 : Nat := 3290891352897676038675607

theorem tailTrace_6408988 : CollatzResearch.WordTrace tailWord_6408988 prefixEnd_6408988 3290891352897676038675607 := by
  unfold tailWord_6408988
  simp only [CollatzResearch.WordTrace]
  refine ⟨116877498052669259426249809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155836664070225679234999745 116877498052669259426249809)
  ·
    refine ⟨87658123539501944569687357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116877498052669259426249809 87658123539501944569687357)
    ·
      refine ⟨32871796327313229213632759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87658123539501944569687357 32871796327313229213632759)
      ·
        refine ⟨49307694490969843820449139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32871796327313229213632759 49307694490969843820449139)
        ·
          refine ⟨73961541736454765730673709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49307694490969843820449139 73961541736454765730673709)
          ·
            refine ⟨27735578151170537149002641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73961541736454765730673709 27735578151170537149002641)
            ·
              refine ⟨20801683613377902861751981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27735578151170537149002641 20801683613377902861751981)
              ·
                refine ⟨7800631355016713573156993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20801683613377902861751981 7800631355016713573156993)
                ·
                  refine ⟨5850473516262535179867745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800631355016713573156993 5850473516262535179867745)
                  ·
                    refine ⟨4387855137196901384900809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5850473516262535179867745 4387855137196901384900809)
                    ·
                      refine ⟨3290891352897676038675607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387855137196901384900809 3290891352897676038675607)
                      ·
                        rfl

theorem cell23_6408988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_6408988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408988 prefixEnd_6408988 := by exact prefixLift 6408988
  have htrace : WordTrace (prefixWord ++ tailWord_6408988) baseStart_6408988 baseEnd_6408988 := by
    simpa [prefixWord, tailWord_6408988, baseEnd_6408988] using wordTrace_append hprefix tailTrace_6408988
  have hstable : (prefixWord ++ tailWord_6408988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408988).length < 2 ^ (prefixWord ++ tailWord_6408988).sum := by decide
  have hdescent : baseEnd_6408988 < baseStart_6408988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6408994 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_6408994 : Nat := 118140960795 + 6408994 * 2 ^ 59
def prefixEnd_6408994 : Nat := 4983230072969 + 3 ^ 40 * 6408994 * 2
def baseEnd_6408994 : Nat := 365654937086844779466731

theorem tailTrace_6408994 : CollatzResearch.WordTrace tailWord_6408994 prefixEnd_6408994 365654937086844779466731 := by
  unfold tailWord_6408994
  simp only [CollatzResearch.WordTrace]
  refine ⟨58438803735829195469304509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155836809962211187918145357 58438803735829195469304509)
  ·
    refine ⟨21914551400935948300989191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58438803735829195469304509 21914551400935948300989191)
    ·
      refine ⟨32871827101403922451483787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21914551400935948300989191 32871827101403922451483787)
      ·
        refine ⟨49307740652105883677225681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32871827101403922451483787 49307740652105883677225681)
        ·
          refine ⟨36980805489079412757919261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49307740652105883677225681 36980805489079412757919261)
          ·
            refine ⟨13867802058404779784219723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36980805489079412757919261 13867802058404779784219723)
            ·
              refine ⟨20801703087607169676329585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13867802058404779784219723 20801703087607169676329585)
              ·
                refine ⟨15601277315705377257247189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20801703087607169676329585 15601277315705377257247189)
                ·
                  refine ⟨365654937086844779466731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15601277315705377257247189 365654937086844779466731)
                  ·
                    rfl

theorem cell23_6408994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_6408994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6408994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6408994 prefixEnd_6408994 := by exact prefixLift 6408994
  have htrace : WordTrace (prefixWord ++ tailWord_6408994) baseStart_6408994 baseEnd_6408994 := by
    simpa [prefixWord, tailWord_6408994, baseEnd_6408994] using wordTrace_append hprefix tailTrace_6408994
  have hstable : (prefixWord ++ tailWord_6408994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6408994).length < 2 ^ (prefixWord ++ tailWord_6408994).sum := by decide
  have hdescent : baseEnd_6408994 < baseStart_6408994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6408994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409011 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 5]
def baseStart_6409011 : Nat := 118140960795 + 6409011 * 2 ^ 59
def prefixEnd_6409011 : Nat := 4983230072969 + 3 ^ 40 * 6409011 * 2
def baseEnd_6409011 : Nat := 365655906994747716520889

theorem tailTrace_6409011 : CollatzResearch.WordTrace tailWord_6409011 prefixEnd_6409011 365655906994747716520889 := by
  unfold tailWord_6409011
  simp only [CollatzResearch.WordTrace]
  refine ⟨233755834984255193780586887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155837223322836795853724591 233755834984255193780586887)
  ·
    refine ⟨350633752476382790670880331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233755834984255193780586887 350633752476382790670880331)
    ·
      refine ⟨525950628714574186006320497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350633752476382790670880331 525950628714574186006320497)
      ·
        refine ⟨394462971535930639504740373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525950628714574186006320497 394462971535930639504740373)
        ·
          refine ⟨18490451790746748726784705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 394462971535930639504740373 18490451790746748726784705)
          ·
            refine ⟨13867838843060061545088529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18490451790746748726784705 13867838843060061545088529)
            ·
              refine ⟨10400879132295046158816397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13867838843060061545088529 10400879132295046158816397)
              ·
                refine ⟨3900329674610642309556149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10400879132295046158816397 3900329674610642309556149)
                ·
                  refine ⟨365655906994747716520889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3900329674610642309556149 365655906994747716520889)
                  ·
                    rfl

theorem cell23_6409011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 5].length) (baseStart_6409011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409011 prefixEnd_6409011 := by exact prefixLift 6409011
  have htrace : WordTrace (prefixWord ++ tailWord_6409011) baseStart_6409011 baseEnd_6409011 := by
    simpa [prefixWord, tailWord_6409011, baseEnd_6409011] using wordTrace_append hprefix tailTrace_6409011
  have hstable : (prefixWord ++ tailWord_6409011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409011).length < 2 ^ (prefixWord ++ tailWord_6409011).sum := by decide
  have hdescent : baseEnd_6409011 < baseStart_6409011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409022 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_6409022 : Nat := 118140960795 + 6409022 * 2 ^ 59
def prefixEnd_6409022 : Nat := 4983230072969 + 3 ^ 40 * 6409022 * 2
def baseEnd_6409022 : Nat := 3290908811239928905650451

theorem tailTrace_6409022 : CollatzResearch.WordTrace tailWord_6409022 prefixEnd_6409022 3290908811239928905650451 := by
  unfold tailWord_6409022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29219529523401917832404665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155837490791476895106158213 29219529523401917832404665)
  ·
    refine ⟨21914647142551438374303499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29219529523401917832404665 21914647142551438374303499)
    ·
      refine ⟨32871970713827157561455249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21914647142551438374303499 32871970713827157561455249)
      ·
        refine ⟨24653978035370368171091437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32871970713827157561455249 24653978035370368171091437)
        ·
          refine ⟨9245241763263888064159289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24653978035370368171091437 9245241763263888064159289)
          ·
            refine ⟨6933931322447916048119467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9245241763263888064159289 6933931322447916048119467)
            ·
              refine ⟨10400896983671874072179201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933931322447916048119467 10400896983671874072179201)
              ·
                refine ⟨7800672737753905554134401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10400896983671874072179201 7800672737753905554134401)
                ·
                  refine ⟨5850504553315429165600801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800672737753905554134401 5850504553315429165600801)
                  ·
                    refine ⟨4387878414986571874200601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5850504553315429165600801 4387878414986571874200601)
                    ·
                      refine ⟨3290908811239928905650451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4387878414986571874200601 3290908811239928905650451)
                      ·
                        rfl

theorem cell23_6409022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_6409022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409022 prefixEnd_6409022 := by exact prefixLift 6409022
  have htrace : WordTrace (prefixWord ++ tailWord_6409022) baseStart_6409022 baseEnd_6409022 := by
    simpa [prefixWord, tailWord_6409022, baseEnd_6409022] using wordTrace_append hprefix tailTrace_6409022
  have hstable : (prefixWord ++ tailWord_6409022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409022).length < 2 ^ (prefixWord ++ tailWord_6409022).sum := by decide
  have hdescent : baseEnd_6409022 < baseStart_6409022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409028 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 7]
def baseStart_6409028 : Nat := 118140960795 + 6409028 * 2 ^ 59
def prefixEnd_6409028 : Nat := 4983230072969 + 3 ^ 40 * 6409028 * 2
def baseEnd_6409028 : Nat := 365656876902650653575047

theorem tailTrace_6409028 : CollatzResearch.WordTrace tailWord_6409028 prefixEnd_6409028 365656876902650653575047 := by
  unfold tailWord_6409028
  simp only [CollatzResearch.WordTrace]
  refine ⟨116878227512596802841977869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155837636683462403789303825 116878227512596802841977869)
  ·
    refine ⟨43829335317223801065741701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116878227512596802841977869 43829335317223801065741701)
    ·
      refine ⟨8218000371979462699826569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43829335317223801065741701 8218000371979462699826569)
      ·
        refine ⟨6163500278984597024869927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8218000371979462699826569 6163500278984597024869927)
        ·
          refine ⟨9245250418476895537304891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163500278984597024869927 9245250418476895537304891)
          ·
            refine ⟨13867875627715343305957337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245250418476895537304891 13867875627715343305957337)
            ·
              refine ⟨10400906720786507479468003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13867875627715343305957337 10400906720786507479468003)
              ·
                refine ⟨15601360081179761219202005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400906720786507479468003 15601360081179761219202005)
                ·
                  refine ⟨365656876902650653575047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15601360081179761219202005 365656876902650653575047)
                  ·
                    rfl

theorem cell23_6409028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_6409028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409028 prefixEnd_6409028 := by exact prefixLift 6409028
  have htrace : WordTrace (prefixWord ++ tailWord_6409028) baseStart_6409028 baseEnd_6409028 := by
    simpa [prefixWord, tailWord_6409028, baseEnd_6409028] using wordTrace_append hprefix tailTrace_6409028
  have hstable : (prefixWord ++ tailWord_6409028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409028).length < 2 ^ (prefixWord ++ tailWord_6409028).sum := by decide
  have hdescent : baseEnd_6409028 < baseStart_6409028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409057 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_6409057 : Nat := 118140960795 + 6409057 * 2 ^ 59
def prefixEnd_6409057 : Nat := 4983230072969 + 3 ^ 40 * 6409057 * 2
def baseEnd_6409057 : Nat := 3290926783062836268712789

theorem tailTrace_6409057 : CollatzResearch.WordTrace tailWord_6409057 prefixEnd_6409057 3290926783062836268712789 := by
  unfold tailWord_6409057
  simp only [CollatzResearch.WordTrace]
  refine ⟨233757512742088543636761425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155838341828059029091174283 233757512742088543636761425)
  ·
    refine ⟨175318134556566407727571069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233757512742088543636761425 175318134556566407727571069)
    ·
      refine ⟨65744300458712402897839151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175318134556566407727571069 65744300458712402897839151)
      ·
        refine ⟨98616450688068604346758727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65744300458712402897839151 98616450688068604346758727)
        ·
          refine ⟨147924676032102906520138091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98616450688068604346758727 147924676032102906520138091)
          ·
            refine ⟨221887014048154359780207137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147924676032102906520138091 221887014048154359780207137)
            ·
              refine ⟨166415260536115769835155353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221887014048154359780207137 166415260536115769835155353)
              ·
                refine ⟨124811445402086827376366515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166415260536115769835155353 124811445402086827376366515)
                ·
                  refine ⟨187217168103130241064549773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124811445402086827376366515 187217168103130241064549773)
                  ·
                    refine ⟨70206438038673840399206165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187217168103130241064549773 70206438038673840399206165)
                    ·
                      refine ⟨3290926783062836268712789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70206438038673840399206165 3290926783062836268712789)
                      ·
                        rfl

theorem cell23_6409057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_6409057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409057 prefixEnd_6409057 := by exact prefixLift 6409057
  have htrace : WordTrace (prefixWord ++ tailWord_6409057) baseStart_6409057 baseEnd_6409057 := by
    simpa [prefixWord, tailWord_6409057, baseEnd_6409057] using wordTrace_append hprefix tailTrace_6409057
  have hstable : (prefixWord ++ tailWord_6409057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409057).length < 2 ^ (prefixWord ++ tailWord_6409057).sum := by decide
  have hdescent : baseEnd_6409057 < baseStart_6409057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409067 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 8]
def baseStart_6409067 : Nat := 118140960795 + 6409067 * 2 ^ 59
def prefixEnd_6409067 : Nat := 4983230072969 + 3 ^ 40 * 6409067 * 2
def baseEnd_6409067 : Nat := 365659101985486803287527

theorem tailTrace_6409067 : CollatzResearch.WordTrace tailWord_6409067 prefixEnd_6409067 365659101985486803287527 := by
  unfold tailWord_6409067
  simp only [CollatzResearch.WordTrace]
  refine ⟨233757877472052315344625455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155838584981368210229750303 233757877472052315344625455)
  ·
    refine ⟨350636816208078473016938183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233757877472052315344625455 350636816208078473016938183)
    ·
      refine ⟨525955224312117709525407275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350636816208078473016938183 525955224312117709525407275)
      ·
        refine ⟨788932836468176564288110913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525955224312117709525407275 788932836468176564288110913)
        ·
          refine ⟨591699627351132423216083185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788932836468176564288110913 591699627351132423216083185)
          ·
            refine ⟨443774720513349317412062389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591699627351132423216083185 443774720513349317412062389)
            ·
              refine ⟨41603880048126498507380849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 443774720513349317412062389 41603880048126498507380849)
              ·
                refine ⟨31202910036094873880535637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41603880048126498507380849 31202910036094873880535637)
                ·
                  refine ⟨365659101985486803287527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31202910036094873880535637 365659101985486803287527)
                  ·
                    rfl

theorem cell23_6409067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 8].length) (baseStart_6409067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409067 prefixEnd_6409067 := by exact prefixLift 6409067
  have htrace : WordTrace (prefixWord ++ tailWord_6409067) baseStart_6409067 baseEnd_6409067 := by
    simpa [prefixWord, tailWord_6409067, baseEnd_6409067] using wordTrace_append hprefix tailTrace_6409067
  have hstable : (prefixWord ++ tailWord_6409067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409067).length < 2 ^ (prefixWord ++ tailWord_6409067).sum := by decide
  have hdescent : baseEnd_6409067 < baseStart_6409067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409078 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6409078 : Nat := 118140960795 + 6409078 * 2 ^ 59
def prefixEnd_6409078 : Nat := 4983230072969 + 3 ^ 40 * 6409078 * 2
def baseEnd_6409078 : Nat := 3290937566156580686550193

theorem tailTrace_6409078 : CollatzResearch.WordTrace tailWord_6409078 prefixEnd_6409078 3290937566156580686550193 := by
  unfold tailWord_6409078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14609892417188279013954743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155838852450008309482183925 14609892417188279013954743)
  ·
    refine ⟨21914838625782418520932115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14609892417188279013954743 21914838625782418520932115)
    ·
      refine ⟨32872257938673627781398173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21914838625782418520932115 32872257938673627781398173)
      ·
        refine ⟨12327096727002610418024315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32872257938673627781398173 12327096727002610418024315)
        ·
          refine ⟨18490645090503915627036473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12327096727002610418024315 18490645090503915627036473)
          ·
            refine ⟨13867983817877936720277355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18490645090503915627036473 13867983817877936720277355)
            ·
              refine ⟨20801975726816905080416033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13867983817877936720277355 20801975726816905080416033)
              ·
                refine ⟨15601481795112678810312025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20801975726816905080416033 15601481795112678810312025)
                ·
                  refine ⟨11701111346334509107734019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15601481795112678810312025 11701111346334509107734019)
                  ·
                    refine ⟨17551667019501763661601029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11701111346334509107734019 17551667019501763661601029)
                    ·
                      refine ⟨3290937566156580686550193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17551667019501763661601029 3290937566156580686550193)
                      ·
                        rfl

theorem cell23_6409078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6409078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409078 prefixEnd_6409078 := by exact prefixLift 6409078
  have htrace : WordTrace (prefixWord ++ tailWord_6409078) baseStart_6409078 baseEnd_6409078 := by
    simpa [prefixWord, tailWord_6409078, baseEnd_6409078] using wordTrace_append hprefix tailTrace_6409078
  have hstable : (prefixWord ++ tailWord_6409078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409078).length < 2 ^ (prefixWord ++ tailWord_6409078).sum := by decide
  have hdescent : baseEnd_6409078 < baseStart_6409078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409081 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_6409081 : Nat := 118140960795 + 6409081 * 2 ^ 59
def prefixEnd_6409081 : Nat := 4983230072969 + 3 ^ 40 * 6409081 * 2
def baseEnd_6409081 : Nat := 3290939106598544174812679

theorem tailTrace_6409081 : CollatzResearch.WordTrace tailWord_6409081 prefixEnd_6409081 3290939106598544174812679 := by
  unfold tailWord_6409081
  simp only [CollatzResearch.WordTrace]
  refine ⟨233758388094001595735635097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155838925396001063823756731 233758388094001595735635097)
  ·
    refine ⟨175318791070501196801726323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233758388094001595735635097 175318791070501196801726323)
    ·
      refine ⟨262978186605751795202589485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175318791070501196801726323 262978186605751795202589485)
      ·
        refine ⟨98616819977156923200971057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262978186605751795202589485 98616819977156923200971057)
        ·
          refine ⟨73962614982867692400728293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98616819977156923200971057 73962614982867692400728293)
          ·
            refine ⟨13867990309287692325136555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73962614982867692400728293 13867990309287692325136555)
            ·
              refine ⟨20801985463931538487704833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13867990309287692325136555 20801985463931538487704833)
              ·
                refine ⟨15601489097948653865778625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20801985463931538487704833 15601489097948653865778625)
                ·
                  refine ⟨11701116823461490399333969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15601489097948653865778625 11701116823461490399333969)
                  ·
                    refine ⟨8775837617596117799500477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11701116823461490399333969 8775837617596117799500477)
                    ·
                      refine ⟨3290939106598544174812679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775837617596117799500477 3290939106598544174812679)
                      ·
                        rfl

theorem cell23_6409081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_6409081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409081 prefixEnd_6409081 := by exact prefixLift 6409081
  have htrace : WordTrace (prefixWord ++ tailWord_6409081) baseStart_6409081 baseEnd_6409081 := by
    simpa [prefixWord, tailWord_6409081, baseEnd_6409081] using wordTrace_append hprefix tailTrace_6409081
  have hstable : (prefixWord ++ tailWord_6409081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409081).length < 2 ^ (prefixWord ++ tailWord_6409081).sum := by decide
  have hdescent : baseEnd_6409081 < baseStart_6409081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409087 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_6409087 : Nat := 118140960795 + 6409087 * 2 ^ 59
def prefixEnd_6409087 : Nat := 4983230072969 + 3 ^ 40 * 6409087 * 2
def baseEnd_6409087 : Nat := 3290942187482471151337651

theorem tailTrace_6409087 : CollatzResearch.WordTrace tailWord_6409087 prefixEnd_6409087 3290942187482471151337651 := by
  unfold tailWord_6409087
  simp only [CollatzResearch.WordTrace]
  refine ⟨233758606931979858760353515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155839071287986572506902343 233758606931979858760353515)
  ·
    refine ⟨350637910397969788140530273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233758606931979858760353515 350637910397969788140530273)
    ·
      refine ⟨262978432798477341105397705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350637910397969788140530273 262978432798477341105397705)
      ·
        refine ⟨197233824598858005829048279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262978432798477341105397705 197233824598858005829048279)
        ·
          refine ⟨295850736898287008743572419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197233824598858005829048279 295850736898287008743572419)
          ·
            refine ⟨443776105347430513115358629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295850736898287008743572419 443776105347430513115358629)
            ·
              refine ⟨83208019752643221209129743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443776105347430513115358629 83208019752643221209129743)
              ·
                refine ⟨124812029628964831813694615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83208019752643221209129743 124812029628964831813694615)
                ·
                  refine ⟨187218044443447247720541923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124812029628964831813694615 187218044443447247720541923)
                  ·
                    refine ⟨280827066665170871580812885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187218044443447247720541923 280827066665170871580812885)
                    ·
                      refine ⟨3290942187482471151337651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 280827066665170871580812885 3290942187482471151337651)
                      ·
                        rfl

theorem cell23_6409087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_6409087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409087 prefixEnd_6409087 := by exact prefixLift 6409087
  have htrace : WordTrace (prefixWord ++ tailWord_6409087) baseStart_6409087 baseEnd_6409087 := by
    simpa [prefixWord, tailWord_6409087, baseEnd_6409087] using wordTrace_append hprefix tailTrace_6409087
  have hstable : (prefixWord ++ tailWord_6409087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409087).length < 2 ^ (prefixWord ++ tailWord_6409087).sum := by decide
  have hdescent : baseEnd_6409087 < baseStart_6409087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409107 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_6409107 : Nat := 118140960795 + 6409107 * 2 ^ 59
def prefixEnd_6409107 : Nat := 4983230072969 + 3 ^ 40 * 6409107 * 2
def baseEnd_6409107 : Nat := 3290952457095561073087559

theorem tailTrace_6409107 : CollatzResearch.WordTrace tailWord_6409107 prefixEnd_6409107 3290952457095561073087559 := by
  unfold tailWord_6409107
  simp only [CollatzResearch.WordTrace]
  refine ⟨233759336391907402176081575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155839557594604934784054383 233759336391907402176081575)
  ·
    refine ⟨350639004587861103264122363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233759336391907402176081575 350639004587861103264122363)
    ·
      refine ⟨525958506881791654896183545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350639004587861103264122363 525958506881791654896183545)
      ·
        refine ⟨394468880161343741172137659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525958506881791654896183545 394468880161343741172137659)
        ·
          refine ⟨591703320242015611758206489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394468880161343741172137659 591703320242015611758206489)
          ·
            refine ⟨443777490181511708818654867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591703320242015611758206489 443777490181511708818654867)
            ·
              refine ⟨665666235272267563227982301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443777490181511708818654867 665666235272267563227982301)
              ·
                refine ⟨249624838227100336210493363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 665666235272267563227982301 249624838227100336210493363)
                ·
                  refine ⟨374437257340650504315740045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249624838227100336210493363 374437257340650504315740045)
                  ·
                    refine ⟨140413971502743939118402517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374437257340650504315740045 140413971502743939118402517)
                    ·
                      refine ⟨3290952457095561073087559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140413971502743939118402517 3290952457095561073087559)
                      ·
                        rfl

theorem cell23_6409107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_6409107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409107 prefixEnd_6409107 := by exact prefixLift 6409107
  have htrace : WordTrace (prefixWord ++ tailWord_6409107) baseStart_6409107 baseEnd_6409107 := by
    simpa [prefixWord, tailWord_6409107, baseEnd_6409107] using wordTrace_append hprefix tailTrace_6409107
  have hstable : (prefixWord ++ tailWord_6409107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409107).length < 2 ^ (prefixWord ++ tailWord_6409107).sum := by decide
  have hdescent : baseEnd_6409107 < baseStart_6409107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409111 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_6409111 : Nat := 118140960795 + 6409111 * 2 ^ 59
def prefixEnd_6409111 : Nat := 4983230072969 + 3 ^ 40 * 6409111 * 2
def baseEnd_6409111 : Nat := 3290954511018179057437541

theorem tailTrace_6409111 : CollatzResearch.WordTrace tailWord_6409111 prefixEnd_6409111 3290954511018179057437541 := by
  unfold tailWord_6409111
  simp only [CollatzResearch.WordTrace]
  refine ⟨233759482283892910859227187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155839654855928607239484791 233759482283892910859227187)
  ·
    refine ⟨350639223425839366288840781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233759482283892910859227187 350639223425839366288840781)
    ·
      refine ⟨131489708784689762358315293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350639223425839366288840781 131489708784689762358315293)
      ·
        refine ⟨49308640794258660884368235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131489708784689762358315293 49308640794258660884368235)
        ·
          refine ⟨73962961191387991326552353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49308640794258660884368235 73962961191387991326552353)
          ·
            refine ⟨55472220893540993494914265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73962961191387991326552353 55472220893540993494914265)
            ·
              refine ⟨41604165670155745121185699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55472220893540993494914265 41604165670155745121185699)
              ·
                refine ⟨62406248505233617681778549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41604165670155745121185699 62406248505233617681778549)
                ·
                  refine ⟨5850585797365651657666739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62406248505233617681778549 5850585797365651657666739)
                  ·
                    refine ⟨8775878696048477486500109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850585797365651657666739 8775878696048477486500109)
                    ·
                      refine ⟨3290954511018179057437541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775878696048477486500109 3290954511018179057437541)
                      ·
                        rfl

theorem cell23_6409111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_6409111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409111 prefixEnd_6409111 := by exact prefixLift 6409111
  have htrace : WordTrace (prefixWord ++ tailWord_6409111) baseStart_6409111 baseEnd_6409111 := by
    simpa [prefixWord, tailWord_6409111, baseEnd_6409111] using wordTrace_append hprefix tailTrace_6409111
  have hstable : (prefixWord ++ tailWord_6409111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409111).length < 2 ^ (prefixWord ++ tailWord_6409111).sum := by decide
  have hdescent : baseEnd_6409111 < baseStart_6409111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409145 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6409145 : Nat := 118140960795 + 6409145 * 2 ^ 59
def prefixEnd_6409145 : Nat := 4983230072969 + 3 ^ 40 * 6409145 * 2
def baseEnd_6409145 : Nat := 3290971969360431924412385

theorem tailTrace_6409145 : CollatzResearch.WordTrace tailWord_6409145 prefixEnd_6409145 3290971969360431924412385 := by
  unfold tailWord_6409145
  simp only [CollatzResearch.WordTrace]
  refine ⟨233760722365769734665964889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155840481577179823110643259 233760722365769734665964889)
  ·
    refine ⟨175320541774327300999473667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233760722365769734665964889 175320541774327300999473667)
    ·
      refine ⟨262980812661490951499210501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175320541774327300999473667 262980812661490951499210501)
      ·
        refine ⟨49308902374029553406101969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262980812661490951499210501 49308902374029553406101969)
        ·
          refine ⟨36981676780522165054576477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49308902374029553406101969 36981676780522165054576477)
          ·
            refine ⟨13868128792695811895466179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36981676780522165054576477 13868128792695811895466179)
            ·
              refine ⟨20802193189043717843199269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13868128792695811895466179 20802193189043717843199269)
              ·
                refine ⟨3900411222945697095599863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20802193189043717843199269 3900411222945697095599863)
                ·
                  refine ⟨5850616834418545643399795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900411222945697095599863 5850616834418545643399795)
                  ·
                    refine ⟨8775925251627818465099693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850616834418545643399795 8775925251627818465099693)
                    ·
                      refine ⟨3290971969360431924412385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8775925251627818465099693 3290971969360431924412385)
                      ·
                        rfl

theorem cell23_6409145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6409145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409145 prefixEnd_6409145 := by exact prefixLift 6409145
  have htrace : WordTrace (prefixWord ++ tailWord_6409145) baseStart_6409145 baseEnd_6409145 := by
    simpa [prefixWord, tailWord_6409145, baseEnd_6409145] using wordTrace_append hprefix tailTrace_6409145
  have hstable : (prefixWord ++ tailWord_6409145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409145).length < 2 ^ (prefixWord ++ tailWord_6409145).sum := by decide
  have hdescent : baseEnd_6409145 < baseStart_6409145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409205 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6409205 : Nat := 118140960795 + 6409205 * 2 ^ 59
def prefixEnd_6409205 : Nat := 4983230072969 + 3 ^ 40 * 6409205 * 2
def baseEnd_6409205 : Nat := 3291002778199701689662109

theorem tailTrace_6409205 : CollatzResearch.WordTrace tailWord_6409205 prefixEnd_6409205 3291002778199701689662109 := by
  unfold tailWord_6409205
  simp only [CollatzResearch.WordTrace]
  refine ⟨233762910745552364913149069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155841940497034909942099379 233762910745552364913149069)
  ·
    refine ⟨87661091529582136842430901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233762910745552364913149069 87661091529582136842430901)
    ·
      refine ⟨8218227330898325328977897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87661091529582136842430901 8218227330898325328977897)
      ·
        refine ⟨6163670498173743996733423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8218227330898325328977897 6163670498173743996733423)
        ·
          refine ⟨9245505747260615995100135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163670498173743996733423 9245505747260615995100135)
          ·
            refine ⟨13868258620890923992650203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245505747260615995100135 13868258620890923992650203)
            ·
              refine ⟨20802387931336385988975305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13868258620890923992650203 20802387931336385988975305)
              ·
                refine ⟨15601790948502289491731479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20802387931336385988975305 15601790948502289491731479)
                ·
                  refine ⟨23402686422753434237597219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15601790948502289491731479 23402686422753434237597219)
                  ·
                    refine ⟨35104029634130151356395829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23402686422753434237597219 35104029634130151356395829)
                    ·
                      refine ⟨3291002778199701689662109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35104029634130151356395829 3291002778199701689662109)
                      ·
                        rfl

theorem cell23_6409205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6409205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409205 prefixEnd_6409205 := by exact prefixLift 6409205
  have htrace : WordTrace (prefixWord ++ tailWord_6409205) baseStart_6409205 baseEnd_6409205 := by
    simpa [prefixWord, tailWord_6409205, baseEnd_6409205] using wordTrace_append hprefix tailTrace_6409205
  have hstable : (prefixWord ++ tailWord_6409205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409205).length < 2 ^ (prefixWord ++ tailWord_6409205).sum := by decide
  have hdescent : baseEnd_6409205 < baseStart_6409205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409278 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6409278 : Nat := 118140960795 + 6409278 * 2 ^ 59
def prefixEnd_6409278 : Nat := 4983230072969 + 3 ^ 40 * 6409278 * 2
def baseEnd_6409278 : Nat := 3291040262287479904049273

theorem tailTrace_6409278 : CollatzResearch.WordTrace tailWord_6409278 prefixEnd_6409278 3291040262287479904049273 := by
  unfold tailWord_6409278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29220696659285987297569561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155843715516191932253704325 29220696659285987297569561)
  ·
    refine ⟨21915522494464490473177171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29220696659285987297569561 21915522494464490473177171)
    ·
      refine ⟨32873283741696735709765757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21915522494464490473177171 32873283741696735709765757)
      ·
        refine ⟨12327481403136275891162159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32873283741696735709765757 12327481403136275891162159)
        ·
          refine ⟨18491222104704413836743239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12327481403136275891162159 18491222104704413836743239)
          ·
            refine ⟨27736833157056620755114859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18491222104704413836743239 27736833157056620755114859)
            ·
              refine ⟨41605249735584931132672289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27736833157056620755114859 41605249735584931132672289)
              ·
                refine ⟨31203937301688698349504217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41605249735584931132672289 31203937301688698349504217)
                ·
                  refine ⟨23402952976266523762128163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31203937301688698349504217 23402952976266523762128163)
                  ·
                    refine ⟨35104429464399785643192245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23402952976266523762128163 35104429464399785643192245)
                    ·
                      refine ⟨3291040262287479904049273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35104429464399785643192245 3291040262287479904049273)
                      ·
                        rfl

theorem cell23_6409278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6409278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409278 prefixEnd_6409278 := by exact prefixLift 6409278
  have htrace : WordTrace (prefixWord ++ tailWord_6409278) baseStart_6409278 baseEnd_6409278 := by
    simpa [prefixWord, tailWord_6409278, baseEnd_6409278] using wordTrace_append hprefix tailTrace_6409278
  have hstable : (prefixWord ++ tailWord_6409278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409278).length < 2 ^ (prefixWord ++ tailWord_6409278).sum := by decide
  have hdescent : baseEnd_6409278 < baseStart_6409278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409308 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_6409308 : Nat := 118140960795 + 6409308 * 2 ^ 59
def prefixEnd_6409308 : Nat := 4983230072969 + 3 ^ 40 * 6409308 * 2
def baseEnd_6409308 : Nat := 3291055666707114786674135

theorem tailTrace_6409308 : CollatzResearch.WordTrace tailWord_6409308 prefixEnd_6409308 3291055666707114786674135 := by
  unfold tailWord_6409308
  simp only [CollatzResearch.WordTrace]
  refine ⟨116883333732089606752074289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155844444976119475669432385 116883333732089606752074289)
  ·
    refine ⟨87662500299067205064055717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116883333732089606752074289 87662500299067205064055717)
    ·
      refine ⟨16436718806075100949510447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87662500299067205064055717 16436718806075100949510447)
      ·
        refine ⟨24655078209112651424265671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16436718806075100949510447 24655078209112651424265671)
        ·
          refine ⟨36982617313668977136398507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24655078209112651424265671 36982617313668977136398507)
          ·
            refine ⟨55473925970503465704597761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36982617313668977136398507 55473925970503465704597761)
            ·
              refine ⟨41605444477877599278448321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55473925970503465704597761 41605444477877599278448321)
              ·
                refine ⟨31204083358408199458836241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41605444477877599278448321 31204083358408199458836241)
                ·
                  refine ⟨23403062518806149594127181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31204083358408199458836241 23403062518806149594127181)
                  ·
                    refine ⟨8776148444552306097797693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23403062518806149594127181 8776148444552306097797693)
                    ·
                      refine ⟨3291055666707114786674135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8776148444552306097797693 3291055666707114786674135)
                      ·
                        rfl

theorem cell23_6409308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_6409308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409308 prefixEnd_6409308 := by exact prefixLift 6409308
  have htrace : WordTrace (prefixWord ++ tailWord_6409308) baseStart_6409308 baseEnd_6409308 := by
    simpa [prefixWord, tailWord_6409308, baseEnd_6409308] using wordTrace_append hprefix tailTrace_6409308
  have hstable : (prefixWord ++ tailWord_6409308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409308).length < 2 ^ (prefixWord ++ tailWord_6409308).sum := by decide
  have hdescent : baseEnd_6409308 < baseStart_6409308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409311 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 2, 5]
def baseStart_6409311 : Nat := 118140960795 + 6409311 * 2 ^ 59
def prefixEnd_6409311 : Nat := 4983230072969 + 3 ^ 40 * 6409311 * 2
def baseEnd_6409311 : Nat := 1097019069049692758312207

theorem tailTrace_6409311 : CollatzResearch.WordTrace tailWord_6409311 prefixEnd_6409311 1097019069049692758312207 := by
  unfold tailWord_6409311
  simp only [CollatzResearch.WordTrace]
  refine ⟨233766776883168345016507787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155844517922112230011005191 233766776883168345016507787)
  ·
    refine ⟨350650165324752517524761681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233766776883168345016507787 350650165324752517524761681)
    ·
      refine ⟨262987623993564388143571261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350650165324752517524761681 262987623993564388143571261)
      ·
        refine ⟨98620358997586645553839223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262987623993564388143571261 98620358997586645553839223)
        ·
          refine ⟨147930538496379968330758835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98620358997586645553839223 147930538496379968330758835)
          ·
            refine ⟨221895807744569952496138253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147930538496379968330758835 221895807744569952496138253)
            ·
              refine ⟨83210927904213732186051845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221895807744569952496138253 83210927904213732186051845)
              ·
                refine ⟨15602048982040074784884721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83210927904213732186051845 15602048982040074784884721)
                ·
                  refine ⟨11701536736530056088663541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15602048982040074784884721 11701536736530056088663541)
                  ·
                    refine ⟨1097019069049692758312207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11701536736530056088663541 1097019069049692758312207)
                    ·
                      rfl

theorem cell23_6409311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_6409311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409311 prefixEnd_6409311 := by exact prefixLift 6409311
  have htrace : WordTrace (prefixWord ++ tailWord_6409311) baseStart_6409311 baseEnd_6409311 := by
    simpa [prefixWord, tailWord_6409311, baseEnd_6409311] using wordTrace_append hprefix tailTrace_6409311
  have hstable : (prefixWord ++ tailWord_6409311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409311).length < 2 ^ (prefixWord ++ tailWord_6409311).sum := by decide
  have hdescent : baseEnd_6409311 < baseStart_6409311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409321 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_6409321 : Nat := 118140960795 + 6409321 * 2 ^ 59
def prefixEnd_6409321 : Nat := 4983230072969 + 3 ^ 40 * 6409321 * 2
def baseEnd_6409321 : Nat := 3291062341955623235811575

theorem tailTrace_6409321 : CollatzResearch.WordTrace tailWord_6409321 prefixEnd_6409321 3291062341955623235811575 := by
  unfold tailWord_6409321
  simp only [CollatzResearch.WordTrace]
  refine ⟨233767141613132116724371817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155844761075421411149581211 233767141613132116724371817)
  ·
    refine ⟨175325356209849087543278863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233767141613132116724371817 175325356209849087543278863)
    ·
      refine ⟨262988034314773631314918295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175325356209849087543278863 262988034314773631314918295)
      ·
        refine ⟨394482051472160446972377443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262988034314773631314918295 394482051472160446972377443)
        ·
          refine ⟨591723077208240670458566165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394482051472160446972377443 591723077208240670458566165)
          ·
            refine ⟨27737019244136281427745289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 591723077208240670458566165 27737019244136281427745289)
            ·
              refine ⟨20802764433102211070808967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27737019244136281427745289 20802764433102211070808967)
              ·
                refine ⟨31204146649653316606213451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20802764433102211070808967 31204146649653316606213451)
                ·
                  refine ⟨46806219974479974909320177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31204146649653316606213451 46806219974479974909320177)
                  ·
                    refine ⟨35104664980859981181990133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46806219974479974909320177 35104664980859981181990133)
                    ·
                      refine ⟨3291062341955623235811575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35104664980859981181990133 3291062341955623235811575)
                      ·
                        rfl

theorem cell23_6409321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_6409321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409321 prefixEnd_6409321 := by exact prefixLift 6409321
  have htrace : WordTrace (prefixWord ++ tailWord_6409321) baseStart_6409321 baseEnd_6409321 := by
    simpa [prefixWord, tailWord_6409321, baseEnd_6409321] using wordTrace_append hprefix tailTrace_6409321
  have hstable : (prefixWord ++ tailWord_6409321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409321).length < 2 ^ (prefixWord ++ tailWord_6409321).sum := by decide
  have hdescent : baseEnd_6409321 < baseStart_6409321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409345 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 2, 5]
def baseStart_6409345 : Nat := 118140960795 + 6409345 * 2 ^ 59
def prefixEnd_6409345 : Nat := 4983230072969 + 3 ^ 40 * 6409345 * 2
def baseEnd_6409345 : Nat := 1097024888497110380637155

theorem tailTrace_6409345 : CollatzResearch.WordTrace tailWord_6409345 prefixEnd_6409345 1097024888497110380637155 := by
  unfold tailWord_6409345
  simp only [CollatzResearch.WordTrace]
  refine ⟨233768016965045168823245489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155845344643363445882163659 233768016965045168823245489)
  ·
    refine ⟨175326012723783876617434117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233768016965045168823245489 175326012723783876617434117)
    ·
      refine ⟨32873627385709476865768897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175326012723783876617434117 32873627385709476865768897)
      ·
        refine ⟨24655220539282107649326673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32873627385709476865768897 24655220539282107649326673)
        ·
          refine ⟨18491415404461580736995005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24655220539282107649326673 18491415404461580736995005)
          ·
            refine ⟨6934280776673092776373127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18491415404461580736995005 6934280776673092776373127)
            ·
              refine ⟨10401421165009639164559691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934280776673092776373127 10401421165009639164559691)
              ·
                refine ⟨15602131747514458746839537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401421165009639164559691 15602131747514458746839537)
                ·
                  refine ⟨11701598810635844060129653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15602131747514458746839537 11701598810635844060129653)
                  ·
                    refine ⟨1097024888497110380637155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11701598810635844060129653 1097024888497110380637155)
                    ·
                      rfl

theorem cell23_6409345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_6409345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409345 prefixEnd_6409345 := by exact prefixLift 6409345
  have htrace : WordTrace (prefixWord ++ tailWord_6409345) baseStart_6409345 baseEnd_6409345 := by
    simpa [prefixWord, tailWord_6409345, baseEnd_6409345] using wordTrace_append hprefix tailTrace_6409345
  have hstable : (prefixWord ++ tailWord_6409345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409345).length < 2 ^ (prefixWord ++ tailWord_6409345).sum := by decide
  have hdescent : baseEnd_6409345 < baseStart_6409345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409348 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_6409348 : Nat := 118140960795 + 6409348 * 2 ^ 59
def prefixEnd_6409348 : Nat := 4983230072969 + 3 ^ 40 * 6409348 * 2
def baseEnd_6409348 : Nat := 3291076205933294630173951

theorem tailTrace_6409348 : CollatzResearch.WordTrace tailWord_6409348 prefixEnd_6409348 3291076205933294630173951 := by
  unfold tailWord_6409348
  simp only [CollatzResearch.WordTrace]
  refine ⟨116884063192017150167802349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155845417589356200223736465 116884063192017150167802349)
  ·
    refine ⟨43831523697006431312925881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116884063192017150167802349 43831523697006431312925881)
    ·
      refine ⟨32873642772754823484694411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43831523697006431312925881 32873642772754823484694411)
      ·
        refine ⟨49310464159132235227041617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32873642772754823484694411 49310464159132235227041617)
        ·
          refine ⟨36982848119349176420281213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49310464159132235227041617 36982848119349176420281213)
          ·
            refine ⟨13868568044755941157605455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36982848119349176420281213 13868568044755941157605455)
            ·
              refine ⟨20802852067133911736408183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13868568044755941157605455 20802852067133911736408183)
              ·
                refine ⟨31204278100700867604612275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20802852067133911736408183 31204278100700867604612275)
                ·
                  refine ⟨46806417151051301406918413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31204278100700867604612275 46806417151051301406918413)
                  ·
                    refine ⟨17552406431644238027594405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46806417151051301406918413 17552406431644238027594405)
                    ·
                      refine ⟨3291076205933294630173951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17552406431644238027594405 3291076205933294630173951)
                      ·
                        rfl

theorem cell23_6409348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_6409348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409348 prefixEnd_6409348 := by exact prefixLift 6409348
  have htrace : WordTrace (prefixWord ++ tailWord_6409348) baseStart_6409348 baseEnd_6409348 := by
    simpa [prefixWord, tailWord_6409348, baseEnd_6409348] using wordTrace_append hprefix tailTrace_6409348
  have hstable : (prefixWord ++ tailWord_6409348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409348).length < 2 ^ (prefixWord ++ tailWord_6409348).sum := by decide
  have hdescent : baseEnd_6409348 < baseStart_6409348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409409 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6409409 : Nat := 118140960795 + 6409409 * 2 ^ 59
def prefixEnd_6409409 : Nat := 4983230072969 + 3 ^ 40 * 6409409 * 2
def baseEnd_6409409 : Nat := 1097035842751072963837057

theorem tailTrace_6409409 : CollatzResearch.WordTrace tailWord_6409409 prefixEnd_6409409 1097035842751072963837057 := by
  unfold tailWord_6409409
  simp only [CollatzResearch.WordTrace]
  refine ⟨233770351236813307753575281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155846900824542205169050187 233770351236813307753575281)
  ·
    refine ⟨175327763427609980815181461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233770351236813307753575281 175327763427609980815181461)
    ·
      refine ⟨8218488910669217850711631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175327763427609980815181461 8218488910669217850711631)
      ·
        refine ⟨12327733366003826776067447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8218488910669217850711631 12327733366003826776067447)
        ·
          refine ⟨18491600049005740164101171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12327733366003826776067447 18491600049005740164101171)
          ·
            refine ⟨27737400073508610246151757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18491600049005740164101171 27737400073508610246151757)
            ·
              refine ⟨10401525027565728842306909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27737400073508610246151757 10401525027565728842306909)
              ·
                refine ⟨3900571885337148315865091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10401525027565728842306909 3900571885337148315865091)
                ·
                  refine ⟨5850857828005722473797637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900571885337148315865091 5850857828005722473797637)
                  ·
                    refine ⟨1097035842751072963837057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850857828005722473797637 1097035842751072963837057)
                    ·
                      rfl

theorem cell23_6409409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6409409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409409 prefixEnd_6409409 := by exact prefixLift 6409409
  have htrace : WordTrace (prefixWord ++ tailWord_6409409) baseStart_6409409 baseEnd_6409409 := by
    simpa [prefixWord, tailWord_6409409, baseEnd_6409409] using wordTrace_append hprefix tailTrace_6409409
  have hstable : (prefixWord ++ tailWord_6409409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409409).length < 2 ^ (prefixWord ++ tailWord_6409409).sum := by decide
  have hdescent : baseEnd_6409409 < baseStart_6409409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409448 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6409448 : Nat := 118140960795 + 6409448 * 2 ^ 59
def prefixEnd_6409448 : Nat := 4983230072969 + 3 ^ 40 * 6409448 * 2
def baseEnd_6409448 : Nat := 1097042517999581412974497

theorem tailTrace_6409448 : CollatzResearch.WordTrace tailWord_6409448 prefixEnd_6409448 1097042517999581412974497 := by
  unfold tailWord_6409448
  simp only [CollatzResearch.WordTrace]
  refine ⟨116885886841836008707122499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155847849122448011609496665 116885886841836008707122499)
  ·
    refine ⟨175328830262754013060683749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116885886841836008707122499 175328830262754013060683749)
    ·
      refine ⟨32874155674266377448878203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175328830262754013060683749 32874155674266377448878203)
      ·
        refine ⟨49311233511399566173317305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32874155674266377448878203 49311233511399566173317305)
        ·
          refine ⟨36983425133549674629987979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49311233511399566173317305 36983425133549674629987979)
          ·
            refine ⟨55475137700324511944981969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36983425133549674629987979 55475137700324511944981969)
            ·
              refine ⟨41606353275243383958736477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55475137700324511944981969 41606353275243383958736477)
              ·
                refine ⟨15602382478216268984526179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41606353275243383958736477 15602382478216268984526179)
                ·
                  refine ⟨23403573717324403476789269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15602382478216268984526179 23403573717324403476789269)
                  ·
                    refine ⟨1097042517999581412974497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23403573717324403476789269 1097042517999581412974497)
                    ·
                      rfl

theorem cell23_6409448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6409448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409448 prefixEnd_6409448 := by exact prefixLift 6409448
  have htrace : WordTrace (prefixWord ++ tailWord_6409448) baseStart_6409448 baseEnd_6409448 := by
    simpa [prefixWord, tailWord_6409448, baseEnd_6409448] using wordTrace_append hprefix tailTrace_6409448
  have hstable : (prefixWord ++ tailWord_6409448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409448).length < 2 ^ (prefixWord ++ tailWord_6409448).sum := by decide
  have hdescent : baseEnd_6409448 < baseStart_6409448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409455 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_6409455 : Nat := 118140960795 + 6409455 * 2 ^ 59
def prefixEnd_6409455 : Nat := 4983230072969 + 3 ^ 40 * 6409455 * 2
def baseEnd_6409455 : Nat := 3291131148363325711535959

theorem tailTrace_6409455 : CollatzResearch.WordTrace tailWord_6409455 prefixEnd_6409455 3291131148363325711535959 := by
  unfold tailWord_6409455
  simp only [CollatzResearch.WordTrace]
  refine ⟨233772028994646657609749819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155848019329764438406499879 233772028994646657609749819)
  ·
    refine ⟨350658043491969986414624729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233772028994646657609749819 350658043491969986414624729)
    ·
      refine ⟨262993532618977489810968547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350658043491969986414624729 262993532618977489810968547)
      ·
        refine ⟨394490298928466234716452821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262993532618977489810968547 394490298928466234716452821)
        ·
          refine ⟨9245866381135927376166863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 394490298928466234716452821 9245866381135927376166863)
          ·
            refine ⟨13868799571703891064250295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245866381135927376166863 13868799571703891064250295)
            ·
              refine ⟨20803199357555836596375443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13868799571703891064250295 20803199357555836596375443)
              ·
                refine ⟨31204799036333754894563165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20803199357555836596375443 31204799036333754894563165)
                ·
                  refine ⟨11701799638625158085461187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31204799036333754894563165 11701799638625158085461187)
                  ·
                    refine ⟨17552699457937737128191781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11701799638625158085461187 17552699457937737128191781)
                    ·
                      refine ⟨3291131148363325711535959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17552699457937737128191781 3291131148363325711535959)
                      ·
                        rfl

theorem cell23_6409455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_6409455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409455 prefixEnd_6409455 := by exact prefixLift 6409455
  have htrace : WordTrace (prefixWord ++ tailWord_6409455) baseStart_6409455 baseEnd_6409455 := by
    simpa [prefixWord, tailWord_6409455, baseEnd_6409455] using wordTrace_append hprefix tailTrace_6409455
  have hstable : (prefixWord ++ tailWord_6409455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409455).length < 2 ^ (prefixWord ++ tailWord_6409455).sum := by decide
  have hdescent : baseEnd_6409455 < baseStart_6409455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409475 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 5]
def baseStart_6409475 : Nat := 118140960795 + 6409475 * 2 ^ 59
def prefixEnd_6409475 : Nat := 4983230072969 + 3 ^ 40 * 6409475 * 2
def baseEnd_6409475 : Nat := 3291141417976415633285867

theorem tailTrace_6409475 : CollatzResearch.WordTrace tailWord_6409475 prefixEnd_6409475 3291141417976415633285867 := by
  unfold tailWord_6409475
  simp only [CollatzResearch.WordTrace]
  refine ⟨233772758454574201025477879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155848505636382800683651919 233772758454574201025477879)
  ·
    refine ⟨350659137681861301538216819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233772758454574201025477879 350659137681861301538216819)
    ·
      refine ⟨525988706522791952307325229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350659137681861301538216819 525988706522791952307325229)
      ·
        refine ⟨197245764946046982115246961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525988706522791952307325229 197245764946046982115246961)
        ·
          refine ⟨147934323709535236586435221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197245764946046982115246961 147934323709535236586435221)
          ·
            refine ⟨6934421423884464214989151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147934323709535236586435221 6934421423884464214989151)
            ·
              refine ⟨10401632135826696322483727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934421423884464214989151 10401632135826696322483727)
              ·
                refine ⟨15602448203740044483725591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401632135826696322483727 15602448203740044483725591)
                ·
                  refine ⟨23403672305610066725588387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15602448203740044483725591 23403672305610066725588387)
                  ·
                    refine ⟨35105508458415100088382581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23403672305610066725588387 35105508458415100088382581)
                    ·
                      refine ⟨3291141417976415633285867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35105508458415100088382581 3291141417976415633285867)
                      ·
                        rfl

theorem cell23_6409475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_6409475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409475 prefixEnd_6409475 := by exact prefixLift 6409475
  have htrace : WordTrace (prefixWord ++ tailWord_6409475) baseStart_6409475 baseEnd_6409475 := by
    simpa [prefixWord, tailWord_6409475, baseEnd_6409475] using wordTrace_append hprefix tailTrace_6409475
  have hstable : (prefixWord ++ tailWord_6409475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409475).length < 2 ^ (prefixWord ++ tailWord_6409475).sum := by decide
  have hdescent : baseEnd_6409475 < baseStart_6409475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409489 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 1, 2, 2]
def baseStart_6409489 : Nat := 118140960795 + 6409489 * 2 ^ 59
def prefixEnd_6409489 : Nat := 4983230072969 + 3 ^ 40 * 6409489 * 2
def baseEnd_6409489 : Nat := 3291148606705578578510803

theorem tailTrace_6409489 : CollatzResearch.WordTrace tailWord_6409489 prefixEnd_6409489 3291148606705578578510803 := by
  unfold tailWord_6409489
  simp only [CollatzResearch.WordTrace]
  refine ⟨233773269076523481416487521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155848846051015654277658347 233773269076523481416487521)
  ·
    refine ⟨175329951807392611062365641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233773269076523481416487521 175329951807392611062365641)
    ·
      refine ⟨131497463855544458296774231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175329951807392611062365641 131497463855544458296774231)
      ·
        refine ⟨197246195783316687445161347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131497463855544458296774231 197246195783316687445161347)
        ·
          refine ⟨295869293674975031167742021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197246195783316687445161347 295869293674975031167742021)
          ·
            refine ⟨55475492564057818343951629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295869293674975031167742021 55475492564057818343951629)
            ·
              refine ⟨20803309711521681878981861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55475492564057818343951629 20803309711521681878981861)
              ·
                refine ⟨3900620570910315352309099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20803309711521681878981861 3900620570910315352309099)
                ·
                  refine ⟨5850930856365473028463649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900620570910315352309099 5850930856365473028463649)
                  ·
                    refine ⟨4388198142274104771347737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5850930856365473028463649 4388198142274104771347737)
                    ·
                      refine ⟨3291148606705578578510803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388198142274104771347737 3291148606705578578510803)
                      ·
                        rfl

theorem cell23_6409489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_6409489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409489 prefixEnd_6409489 := by exact prefixLift 6409489
  have htrace : WordTrace (prefixWord ++ tailWord_6409489) baseStart_6409489 baseEnd_6409489 := by
    simpa [prefixWord, tailWord_6409489, baseEnd_6409489] using wordTrace_append hprefix tailTrace_6409489
  have hstable : (prefixWord ++ tailWord_6409489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409489).length < 2 ^ (prefixWord ++ tailWord_6409489).sum := by decide
  have hdescent : baseEnd_6409489 < baseStart_6409489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409505 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_6409505 : Nat := 118140960795 + 6409505 * 2 ^ 59
def prefixEnd_6409505 : Nat := 4983230072969 + 3 ^ 40 * 6409505 * 2
def baseEnd_6409505 : Nat := 3291156822396050515910729

theorem tailTrace_6409505 : CollatzResearch.WordTrace tailWord_6409505 prefixEnd_6409505 3291156822396050515910729 := by
  unfold tailWord_6409505
  simp only [CollatzResearch.WordTrace]
  refine ⟨233773852644465516149069969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155849235096310344099379979 233773852644465516149069969)
  ·
    refine ⟨175330389483349137111802477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233773852644465516149069969 175330389483349137111802477)
    ·
      refine ⟨65748896056255926416925929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175330389483349137111802477 65748896056255926416925929)
      ·
        refine ⟨49311672042191944812694447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65748896056255926416925929 49311672042191944812694447)
        ·
          refine ⟨73967508063287917219041671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49311672042191944812694447 73967508063287917219041671)
          ·
            refine ⟨110951262094931875828562507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73967508063287917219041671 110951262094931875828562507)
            ·
              refine ⟨166426893142397813742843761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110951262094931875828562507 166426893142397813742843761)
              ·
                refine ⟨124820169856798360307132821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166426893142397813742843761 124820169856798360307132821)
                ·
                  refine ⟨5850945462037423139396851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124820169856798360307132821 5850945462037423139396851)
                  ·
                    refine ⟨8776418193056134709095277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850945462037423139396851 8776418193056134709095277)
                    ·
                      refine ⟨3291156822396050515910729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8776418193056134709095277 3291156822396050515910729)
                      ·
                        rfl

theorem cell23_6409505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_6409505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409505 prefixEnd_6409505 := by exact prefixLift 6409505
  have htrace : WordTrace (prefixWord ++ tailWord_6409505) baseStart_6409505 baseEnd_6409505 := by
    simpa [prefixWord, tailWord_6409505, baseEnd_6409505] using wordTrace_append hprefix tailTrace_6409505
  have hstable : (prefixWord ++ tailWord_6409505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409505).length < 2 ^ (prefixWord ++ tailWord_6409505).sum := by decide
  have hdescent : baseEnd_6409505 < baseStart_6409505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409508 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_6409508 : Nat := 118140960795 + 6409508 * 2 ^ 59
def prefixEnd_6409508 : Nat := 4983230072969 + 3 ^ 40 * 6409508 * 2
def baseEnd_6409508 : Nat := 1097052787612671334724405

theorem tailTrace_6409508 : CollatzResearch.WordTrace tailWord_6409508 prefixEnd_6409508 1097052787612671334724405 := by
  unfold tailWord_6409508
  simp only [CollatzResearch.WordTrace]
  refine ⟨116886981031727323830714589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155849308042303098440952785 116886981031727323830714589)
  ·
    refine ⟨43832617886897746436517971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116886981031727323830714589 43832617886897746436517971)
    ·
      refine ⟨65748926830346619654776957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43832617886897746436517971 65748926830346619654776957)
      ·
        refine ⟨24655847561379982370541359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65748926830346619654776957 24655847561379982370541359)
        ·
          refine ⟨36983771342069973555812039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24655847561379982370541359 36983771342069973555812039)
          ·
            refine ⟨55475657013104960333718059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36983771342069973555812039 55475657013104960333718059)
            ·
              refine ⟨83213485519657440500577089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55475657013104960333718059 83213485519657440500577089)
              ·
                refine ⟨62410114139743080375432817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83213485519657440500577089 62410114139743080375432817)
                ·
                  refine ⟨46807585604807310281574613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62410114139743080375432817 46807585604807310281574613)
                  ·
                    refine ⟨1097052787612671334724405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46807585604807310281574613 1097052787612671334724405)
                    ·
                      rfl

theorem cell23_6409508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_6409508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409508 prefixEnd_6409508 := by exact prefixLift 6409508
  have htrace : WordTrace (prefixWord ++ tailWord_6409508) baseStart_6409508 baseEnd_6409508 := by
    simpa [prefixWord, tailWord_6409508, baseEnd_6409508] using wordTrace_append hprefix tailTrace_6409508
  have hstable : (prefixWord ++ tailWord_6409508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409508).length < 2 ^ (prefixWord ++ tailWord_6409508).sum := by decide
  have hdescent : baseEnd_6409508 < baseStart_6409508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409526 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6409526 : Nat := 118140960795 + 6409526 * 2 ^ 59
def prefixEnd_6409526 : Nat := 4983230072969 + 3 ^ 40 * 6409526 * 2
def baseEnd_6409526 : Nat := 3291167605489794933748133

theorem tailTrace_6409526 : CollatzResearch.WordTrace tailWord_6409526 prefixEnd_6409526 3291167605489794933748133 := by
  unfold tailWord_6409526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14610913661086839795974027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155849745718259624490389621 14610913661086839795974027)
  ·
    refine ⟨21916370491630259693961041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14610913661086839795974027 21916370491630259693961041)
    ·
      refine ⟨16437277868722694770470781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21916370491630259693961041 16437277868722694770470781)
      ·
        refine ⟨6163979200771010538926543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16437277868722694770470781 6163979200771010538926543)
        ·
          refine ⟨9245968801156515808389815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163979200771010538926543 9245968801156515808389815)
          ·
            refine ⟨13868953201734773712584723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245968801156515808389815 13868953201734773712584723)
            ·
              refine ⟨20803429802602160568877085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13868953201734773712584723 20803429802602160568877085)
              ·
                refine ⟨7801286175975810213328907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20803429802602160568877085 7801286175975810213328907)
                ·
                  refine ⟨11701929263963715319993361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7801286175975810213328907 11701929263963715319993361)
                  ·
                    refine ⟨8776446947972786489995021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11701929263963715319993361 8776446947972786489995021)
                    ·
                      refine ⟨3291167605489794933748133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8776446947972786489995021 3291167605489794933748133)
                      ·
                        rfl

theorem cell23_6409526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6409526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409526 prefixEnd_6409526 := by exact prefixLift 6409526
  have htrace : WordTrace (prefixWord ++ tailWord_6409526) baseStart_6409526 baseEnd_6409526 := by
    simpa [prefixWord, tailWord_6409526, baseEnd_6409526] using wordTrace_append hprefix tailTrace_6409526
  have hstable : (prefixWord ++ tailWord_6409526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409526).length < 2 ^ (prefixWord ++ tailWord_6409526).sum := by decide
  have hdescent : baseEnd_6409526 < baseStart_6409526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409545 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 3, 4, 2]
def baseStart_6409545 : Nat := 118140960795 + 6409545 * 2 ^ 59
def prefixEnd_6409545 : Nat := 4983230072969 + 3 ^ 40 * 6409545 * 2
def baseEnd_6409545 : Nat := 3291177361622230359410545

theorem tailTrace_6409545 : CollatzResearch.WordTrace tailWord_6409545 prefixEnd_6409545 3291177361622230359410545 := by
  unfold tailWord_6409545
  simp only [CollatzResearch.WordTrace]
  refine ⟨233775311564320602980526089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155850207709547068653684059 233775311564320602980526089)
  ·
    refine ⟨175331483673240452235394567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233775311564320602980526089 175331483673240452235394567)
    ·
      refine ⟨262997225509860678353091851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175331483673240452235394567 262997225509860678353091851)
      ·
        refine ⟨394495838264791017529637777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262997225509860678353091851 394495838264791017529637777)
        ·
          refine ⟨295871878698593263147228333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394495838264791017529637777 295871878698593263147228333)
          ·
            refine ⟨110951954511972473680210625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295871878698593263147228333 110951954511972473680210625)
            ·
              refine ⟨83213965883979355260157969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110951954511972473680210625 83213965883979355260157969)
              ·
                refine ⟨62410474412984516445118477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83213965883979355260157969 62410474412984516445118477)
                ·
                  refine ⟨23403927904869193666919429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62410474412984516445118477 23403927904869193666919429)
                  ·
                    refine ⟨4388236482162973812547393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23403927904869193666919429 4388236482162973812547393)
                    ·
                      refine ⟨3291177361622230359410545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388236482162973812547393 3291177361622230359410545)
                      ·
                        rfl

theorem cell23_6409545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 4, 2].length) (baseStart_6409545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409545 prefixEnd_6409545 := by exact prefixLift 6409545
  have htrace : WordTrace (prefixWord ++ tailWord_6409545) baseStart_6409545 baseEnd_6409545 := by
    simpa [prefixWord, tailWord_6409545, baseEnd_6409545] using wordTrace_append hprefix tailTrace_6409545
  have hstable : (prefixWord ++ tailWord_6409545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409545).length < 2 ^ (prefixWord ++ tailWord_6409545).sum := by decide
  have hdescent : baseEnd_6409545 < baseStart_6409545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409562 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2]
def baseStart_6409562 : Nat := 118140960795 + 6409562 * 2 ^ 59
def prefixEnd_6409562 : Nat := 4983230072969 + 3 ^ 40 * 6409562 * 2
def baseEnd_6409562 : Nat := 3291186090793356792897967

theorem tailTrace_6409562 : CollatzResearch.WordTrace tailWord_6409562 prefixEnd_6409562 3291186090793356792897967 := by
  unfold tailWord_6409562
  simp only [CollatzResearch.WordTrace]
  refine ⟨58443982901314753720973735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155850621070172676589263293 58443982901314753720973735)
  ·
    refine ⟨87665974351972130581460603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58443982901314753720973735 87665974351972130581460603)
    ·
      refine ⟨131498961527958195872190905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87665974351972130581460603 131498961527958195872190905)
      ·
        refine ⟨98624221145968646904143179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131498961527958195872190905 98624221145968646904143179)
        ·
          refine ⟨147936331718952970356214769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98624221145968646904143179 147936331718952970356214769)
          ·
            refine ⟨110952248789214727767161077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147936331718952970356214769 110952248789214727767161077)
            ·
              refine ⟨10401773323988880728171351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110952248789214727767161077 10401773323988880728171351)
              ·
                refine ⟨15602659985983321092257027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401773323988880728171351 15602659985983321092257027)
                ·
                  refine ⟨23403989978974981638385541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15602659985983321092257027 23403989978974981638385541)
                  ·
                    refine ⟨4388248121057809057197289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23403989978974981638385541 4388248121057809057197289)
                    ·
                      refine ⟨3291186090793356792897967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388248121057809057197289 3291186090793356792897967)
                      ·
                        rfl

theorem cell23_6409562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_6409562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409562 prefixEnd_6409562 := by exact prefixLift 6409562
  have htrace : WordTrace (prefixWord ++ tailWord_6409562) baseStart_6409562 baseEnd_6409562 := by
    simpa [prefixWord, tailWord_6409562, baseEnd_6409562] using wordTrace_append hprefix tailTrace_6409562
  have hstable : (prefixWord ++ tailWord_6409562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409562).length < 2 ^ (prefixWord ++ tailWord_6409562).sum := by decide
  have hdescent : baseEnd_6409562 < baseStart_6409562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409662 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_6409662 : Nat := 118140960795 + 6409662 * 2 ^ 59
def prefixEnd_6409662 : Nat := 4983230072969 + 3 ^ 40 * 6409662 * 2
def baseEnd_6409662 : Nat := 1097079146286268800549169

theorem tailTrace_6409662 : CollatzResearch.WordTrace tailWord_6409662 prefixEnd_6409662 1097079146286268800549169 := by
  unfold tailWord_6409662
  simp only [CollatzResearch.WordTrace]
  refine ⟨29222447363112091495316905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155853052603264487975023493 29222447363112091495316905)
  ·
    refine ⟨21916835522334068621487679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29222447363112091495316905 21916835522334068621487679)
    ·
      refine ⟨32875253283501102932231519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21916835522334068621487679 32875253283501102932231519)
      ·
        refine ⟨49312879925251654398347279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32875253283501102932231519 49312879925251654398347279)
        ·
          refine ⟨73969319887877481597520919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49312879925251654398347279 73969319887877481597520919)
          ·
            refine ⟨110953979831816222396281379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73969319887877481597520919 110953979831816222396281379)
            ·
              refine ⟨166430969747724333594422069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110953979831816222396281379 166430969747724333594422069)
              ·
                refine ⟨15602903413849156274477069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166430969747724333594422069 15602903413849156274477069)
                ·
                  refine ⟨5851088780193433602928901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15602903413849156274477069 5851088780193433602928901)
                  ·
                    refine ⟨1097079146286268800549169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851088780193433602928901 1097079146286268800549169)
                    ·
                      rfl

theorem cell23_6409662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_6409662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409662 prefixEnd_6409662 := by exact prefixLift 6409662
  have htrace : WordTrace (prefixWord ++ tailWord_6409662) baseStart_6409662 baseEnd_6409662 := by
    simpa [prefixWord, tailWord_6409662, baseEnd_6409662] using wordTrace_append hprefix tailTrace_6409662
  have hstable : (prefixWord ++ tailWord_6409662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409662).length < 2 ^ (prefixWord ++ tailWord_6409662).sum := by decide
  have hdescent : baseEnd_6409662 < baseStart_6409662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409675 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 6]
def baseStart_6409675 : Nat := 118140960795 + 6409675 * 2 ^ 59
def prefixEnd_6409675 : Nat := 4983230072969 + 3 ^ 40 * 6409675 * 2
def baseEnd_6409675 : Nat := 365693790456368316753883

theorem tailTrace_6409675 : CollatzResearch.WordTrace tailWord_6409675 prefixEnd_6409675 365693790456368316753883 := by
  unfold tailWord_6409675
  simp only [CollatzResearch.WordTrace]
  refine ⟨233780053053849635182758479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155853368702566423455172319 233780053053849635182758479)
  ·
    refine ⟨350670079580774452774137719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233780053053849635182758479 350670079580774452774137719)
    ·
      refine ⟨526005119371161679161206579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350670079580774452774137719 526005119371161679161206579)
      ·
        refine ⟨789007679056742518741809869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526005119371161679161206579 789007679056742518741809869)
        ·
          refine ⟨295877879646278444528178701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789007679056742518741809869 295877879646278444528178701)
          ·
            refine ⟨110954204867354416698067013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295877879646278444528178701 110954204867354416698067013)
            ·
              refine ⟨20803913412628953130887565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110954204867354416698067013 20803913412628953130887565)
              ·
                refine ⟨7801467529735857424082837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20803913412628953130887565 7801467529735857424082837)
                ·
                  refine ⟨365693790456368316753883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7801467529735857424082837 365693790456368316753883)
                  ·
                    rfl

theorem cell23_6409675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 6].length) (baseStart_6409675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409675 prefixEnd_6409675 := by exact prefixLift 6409675
  have htrace : WordTrace (prefixWord ++ tailWord_6409675) baseStart_6409675 baseEnd_6409675 := by
    simpa [prefixWord, tailWord_6409675, baseEnd_6409675] using wordTrace_append hprefix tailTrace_6409675
  have hstable : (prefixWord ++ tailWord_6409675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409675).length < 2 ^ (prefixWord ++ tailWord_6409675).sum := by decide
  have hdescent : baseEnd_6409675 < baseStart_6409675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409686 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6409686 : Nat := 118140960795 + 6409686 * 2 ^ 59
def prefixEnd_6409686 : Nat := 4983230072969 + 3 ^ 40 * 6409686 * 2
def baseEnd_6409686 : Nat := 3291249762394514307747397

theorem tailTrace_6409686 : CollatzResearch.WordTrace tailWord_6409686 prefixEnd_6409686 3291249762394514307747397 := by
  unfold tailWord_6409686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611278391050611503838057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155853636171206522707605941 14611278391050611503838057)
  ·
    refine ⟨10958458793287958627878543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14611278391050611503838057 10958458793287958627878543)
    ·
      refine ⟨16437688189931937941817815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10958458793287958627878543 16437688189931937941817815)
      ·
        refine ⟨24656532284897906912726723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16437688189931937941817815 24656532284897906912726723)
        ·
          refine ⟨36984798427346860369090085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24656532284897906912726723 36984798427346860369090085)
          ·
            refine ⟨6934649705127536319204391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36984798427346860369090085 6934649705127536319204391)
            ·
              refine ⟨10401974557691304478806587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934649705127536319204391 10401974557691304478806587)
              ·
                refine ⟨15602961836536956718209881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401974557691304478806587 15602961836536956718209881)
                ·
                  refine ⟨11702221377402717538657411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15602961836536956718209881 11702221377402717538657411)
                  ·
                    refine ⟨17553332066104076307986117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11702221377402717538657411 17553332066104076307986117)
                    ·
                      refine ⟨3291249762394514307747397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17553332066104076307986117 3291249762394514307747397)
                      ·
                        rfl

theorem cell23_6409686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6409686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409686 prefixEnd_6409686 := by exact prefixLift 6409686
  have htrace : WordTrace (prefixWord ++ tailWord_6409686) baseStart_6409686 baseEnd_6409686 := by
    simpa [prefixWord, tailWord_6409686, baseEnd_6409686] using wordTrace_append hprefix tailTrace_6409686
  have hstable : (prefixWord ++ tailWord_6409686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409686).length < 2 ^ (prefixWord ++ tailWord_6409686).sum := by decide
  have hdescent : baseEnd_6409686 < baseStart_6409686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409689 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 3]
def baseStart_6409689 : Nat := 118140960795 + 6409689 * 2 ^ 59
def prefixEnd_6409689 : Nat := 4983230072969 + 3 ^ 40 * 6409689 * 2
def baseEnd_6409689 : Nat := 3291251302836477796009883

theorem tailTrace_6409689 : CollatzResearch.WordTrace tailWord_6409689 prefixEnd_6409689 3291251302836477796009883 := by
  unfold tailWord_6409689
  simp only [CollatzResearch.WordTrace]
  refine ⟨233780563675798915573768121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155853709117199277049178747 233780563675798915573768121)
  ·
    refine ⟨175335422756849186680326091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233780563675798915573768121 175335422756849186680326091)
    ·
      refine ⟨263003134135273780020489137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175335422756849186680326091 263003134135273780020489137)
      ·
        refine ⟨197252350601455335015366853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263003134135273780020489137 197252350601455335015366853)
        ·
          refine ⟨36984815737772875315381285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197252350601455335015366853 36984815737772875315381285)
          ·
            refine ⟨6934652950832414121633991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36984815737772875315381285 6934652950832414121633991)
            ·
              refine ⟨10401979426248621182450987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934652950832414121633991 10401979426248621182450987)
              ·
                refine ⟨15602969139372931773676481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401979426248621182450987 15602969139372931773676481)
                ·
                  refine ⟨11702226854529698830257361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15602969139372931773676481 11702226854529698830257361)
                  ·
                    refine ⟨8776670140897274122693021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11702226854529698830257361 8776670140897274122693021)
                    ·
                      refine ⟨3291251302836477796009883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8776670140897274122693021 3291251302836477796009883)
                      ·
                        rfl

theorem cell23_6409689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_6409689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409689 prefixEnd_6409689 := by exact prefixLift 6409689
  have htrace : WordTrace (prefixWord ++ tailWord_6409689) baseStart_6409689 baseEnd_6409689 := by
    simpa [prefixWord, tailWord_6409689, baseEnd_6409689] using wordTrace_append hprefix tailTrace_6409689
  have hstable : (prefixWord ++ tailWord_6409689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409689).length < 2 ^ (prefixWord ++ tailWord_6409689).sum := by decide
  have hdescent : baseEnd_6409689 < baseStart_6409689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409739 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 1, 5]
def baseStart_6409739 : Nat := 118140960795 + 6409739 * 2 ^ 59
def prefixEnd_6409739 : Nat := 4983230072969 + 3 ^ 40 * 6409739 * 2
def baseEnd_6409739 : Nat := 1097092325623067533461551

theorem tailTrace_6409739 : CollatzResearch.WordTrace tailWord_6409739 prefixEnd_6409739 1097092325623067533461551 := by
  unfold tailWord_6409739
  simp only [CollatzResearch.WordTrace]
  refine ⟨233782387325617774113088271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155854924883745182742058847 233782387325617774113088271)
  ·
    refine ⟨350673580988426661169632407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233782387325617774113088271 350673580988426661169632407)
    ·
      refine ⟨526010371482639991754448611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350673580988426661169632407 526010371482639991754448611)
      ·
        refine ⟨789015557223959987631672917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526010371482639991754448611 789015557223959987631672917)
        ·
          refine ⟨9246276061218281105058667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 789015557223959987631672917 9246276061218281105058667)
          ·
            refine ⟨13869414091827421657588001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9246276061218281105058667 13869414091827421657588001)
            ·
              refine ⟨10402060568870566243191001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13869414091827421657588001 10402060568870566243191001)
              ·
                refine ⟨7801545426652924682393251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10402060568870566243191001 7801545426652924682393251)
                ·
                  refine ⟨11702318139979387023589877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7801545426652924682393251 11702318139979387023589877)
                  ·
                    refine ⟨1097092325623067533461551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11702318139979387023589877 1097092325623067533461551)
                    ·
                      rfl

theorem cell23_6409739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 5].length) (baseStart_6409739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409739 prefixEnd_6409739 := by exact prefixLift 6409739
  have htrace : WordTrace (prefixWord ++ tailWord_6409739) baseStart_6409739 baseEnd_6409739 := by
    simpa [prefixWord, tailWord_6409739, baseEnd_6409739] using wordTrace_append hprefix tailTrace_6409739
  have hstable : (prefixWord ++ tailWord_6409739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409739).length < 2 ^ (prefixWord ++ tailWord_6409739).sum := by decide
  have hdescent : baseEnd_6409739 < baseStart_6409739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409745 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_6409745 : Nat := 118140960795 + 6409745 * 2 ^ 59
def prefixEnd_6409745 : Nat := 4983230072969 + 3 ^ 40 * 6409745 * 2
def baseEnd_6409745 : Nat := 3291280057753129576909625

theorem tailTrace_6409745 : CollatzResearch.WordTrace tailWord_6409745 prefixEnd_6409745 3291280057753129576909625 := by
  unfold tailWord_6409745
  simp only [CollatzResearch.WordTrace]
  refine ⟨233782606163596037137806689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155855070775730691425204459 233782606163596037137806689)
  ·
    refine ⟨175336954622697027853355017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233782606163596037137806689 175336954622697027853355017)
    ·
      refine ⟨131502715967022770890016263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175336954622697027853355017 131502715967022770890016263)
      ·
        refine ⟨197254073950534156335024395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131502715967022770890016263 197254073950534156335024395)
        ·
          refine ⟨295881110925801234502536593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197254073950534156335024395 295881110925801234502536593)
          ·
            refine ⟨221910833194350925876902445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295881110925801234502536593 221910833194350925876902445)
            ·
              refine ⟨83216562447881597203838417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221910833194350925876902445 83216562447881597203838417)
              ·
                refine ⟨62412421835911197902878813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83216562447881597203838417 62412421835911197902878813)
                ·
                  refine ⟨23404658188466699213579555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62412421835911197902878813 23404658188466699213579555)
                  ·
                    refine ⟨35106987282700048820369333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23404658188466699213579555 35106987282700048820369333)
                    ·
                      refine ⟨3291280057753129576909625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35106987282700048820369333 3291280057753129576909625)
                      ·
                        rfl

theorem cell23_6409745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_6409745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409745 prefixEnd_6409745 := by exact prefixLift 6409745
  have htrace : WordTrace (prefixWord ++ tailWord_6409745) baseStart_6409745 baseEnd_6409745 := by
    simpa [prefixWord, tailWord_6409745, baseEnd_6409745] using wordTrace_append hprefix tailTrace_6409745
  have hstable : (prefixWord ++ tailWord_6409745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409745).length < 2 ^ (prefixWord ++ tailWord_6409745).sum := by decide
  have hdescent : baseEnd_6409745 < baseStart_6409745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409759 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 5, 2, 2]
def baseStart_6409759 : Nat := 118140960795 + 6409759 * 2 ^ 59
def prefixEnd_6409759 : Nat := 4983230072969 + 3 ^ 40 * 6409759 * 2
def baseEnd_6409759 : Nat := 3291287246482292522134561

theorem tailTrace_6409759 : CollatzResearch.WordTrace tailWord_6409759 prefixEnd_6409759 3291287246482292522134561 := by
  unfold tailWord_6409759
  simp only [CollatzResearch.WordTrace]
  refine ⟨233783116785545317528816331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155855411190363545019210887 233783116785545317528816331)
  ·
    refine ⟨350674675178317976293224497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233783116785545317528816331 350674675178317976293224497)
    ·
      refine ⟨263006006383738482219918373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350674675178317976293224497 263006006383738482219918373)
      ·
        refine ⟨49313626196950965416234695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263006006383738482219918373 49313626196950965416234695)
        ·
          refine ⟨73970439295426448124352043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49313626196950965416234695 73970439295426448124352043)
          ·
            refine ⟨110955658943139672186528065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73970439295426448124352043 110955658943139672186528065)
            ·
              refine ⟨83216744207354754139896049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110955658943139672186528065 83216744207354754139896049)
              ·
                refine ⟨62412558155516065604922037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83216744207354754139896049 62412558155516065604922037)
                ·
                  refine ⟨5851177327079631150461441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62412558155516065604922037 5851177327079631150461441)
                  ·
                    refine ⟨4388382995309723362846081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5851177327079631150461441 4388382995309723362846081)
                    ·
                      refine ⟨3291287246482292522134561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388382995309723362846081 3291287246482292522134561)
                      ·
                        rfl

theorem cell23_6409759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_6409759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409759 prefixEnd_6409759 := by exact prefixLift 6409759
  have htrace : WordTrace (prefixWord ++ tailWord_6409759) baseStart_6409759 baseEnd_6409759 := by
    simpa [prefixWord, tailWord_6409759, baseEnd_6409759] using wordTrace_append hprefix tailTrace_6409759
  have hstable : (prefixWord ++ tailWord_6409759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409759).length < 2 ^ (prefixWord ++ tailWord_6409759).sum := by decide
  have hdescent : baseEnd_6409759 < baseStart_6409759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409762 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_6409762 : Nat := 118140960795 + 6409762 * 2 ^ 59
def prefixEnd_6409762 : Nat := 4983230072969 + 3 ^ 40 * 6409762 * 2
def baseEnd_6409762 : Nat := 3291288786924256010397047

theorem tailTrace_6409762 : CollatzResearch.WordTrace tailWord_6409762 prefixEnd_6409762 3291288786924256010397047 := by
  unfold tailWord_6409762
  simp only [CollatzResearch.WordTrace]
  refine ⟨58445806551133612260293885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155855484136356299360783693 58445806551133612260293885)
  ·
    refine ⟨21917177456675104597610207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58445806551133612260293885 21917177456675104597610207)
    ·
      refine ⟨32875766185012656896415311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21917177456675104597610207 32875766185012656896415311)
      ·
        refine ⟨49313649277518985344622967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32875766185012656896415311 49313649277518985344622967)
        ·
          refine ⟨73970473916278478016934451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49313649277518985344622967 73970473916278478016934451)
          ·
            refine ⟨110955710874417717025401677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73970473916278478016934451 110955710874417717025401677)
            ·
              refine ⟨41608391577906643884525629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110955710874417717025401677 41608391577906643884525629)
              ·
                refine ⟨15603146841714991456697111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41608391577906643884525629 15603146841714991456697111)
                ·
                  refine ⟨23404720262572487185045667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15603146841714991456697111 23404720262572487185045667)
                  ·
                    refine ⟨35107080393858730777568501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23404720262572487185045667 35107080393858730777568501)
                    ·
                      refine ⟨3291288786924256010397047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35107080393858730777568501 3291288786924256010397047)
                      ·
                        rfl

theorem cell23_6409762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_6409762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409762 prefixEnd_6409762 := by exact prefixLift 6409762
  have htrace : WordTrace (prefixWord ++ tailWord_6409762) baseStart_6409762 baseEnd_6409762 := by
    simpa [prefixWord, tailWord_6409762, baseEnd_6409762] using wordTrace_append hprefix tailTrace_6409762
  have hstable : (prefixWord ++ tailWord_6409762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409762).length < 2 ^ (prefixWord ++ tailWord_6409762).sum := by decide
  have hdescent : baseEnd_6409762 < baseStart_6409762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409792 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_6409792 : Nat := 118140960795 + 6409792 * 2 ^ 59
def prefixEnd_6409792 : Nat := 4983230072969 + 3 ^ 40 * 6409792 * 2
def baseEnd_6409792 : Nat := 3291304191343890893021909

theorem tailTrace_6409792 : CollatzResearch.WordTrace tailWord_6409792 prefixEnd_6409792 3291304191343890893021909 := by
  unfold tailWord_6409792
  simp only [CollatzResearch.WordTrace]
  refine ⟨116892160197212882082383815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155856213596283842776511753 116892160197212882082383815)
  ·
    refine ⟨175338240295819323123575723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116892160197212882082383815 175338240295819323123575723)
    ·
      refine ⟨263007360443728984685363585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175338240295819323123575723 263007360443728984685363585)
      ·
        refine ⟨197255520332796738514022689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263007360443728984685363585 197255520332796738514022689)
        ·
          refine ⟨147941640249597553885517017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197255520332796738514022689 147941640249597553885517017)
          ·
            refine ⟨110956230187198165414137763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147941640249597553885517017 110956230187198165414137763)
            ·
              refine ⟨166434345280797248121206645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110956230187198165414137763 166434345280797248121206645)
              ·
                refine ⟨15603219870074742011363123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166434345280797248121206645 15603219870074742011363123)
                ·
                  refine ⟨23404829805112113017044685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15603219870074742011363123 23404829805112113017044685)
                  ·
                    refine ⟨8776811176917042381391757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23404829805112113017044685 8776811176917042381391757)
                    ·
                      refine ⟨3291304191343890893021909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8776811176917042381391757 3291304191343890893021909)
                      ·
                        rfl

theorem cell23_6409792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_6409792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409792 prefixEnd_6409792 := by exact prefixLift 6409792
  have htrace : WordTrace (prefixWord ++ tailWord_6409792) baseStart_6409792 baseEnd_6409792 := by
    simpa [prefixWord, tailWord_6409792, baseEnd_6409792] using wordTrace_append hprefix tailTrace_6409792
  have hstable : (prefixWord ++ tailWord_6409792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409792).length < 2 ^ (prefixWord ++ tailWord_6409792).sum := by decide
  have hdescent : baseEnd_6409792 < baseStart_6409792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409842 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_6409842 : Nat := 118140960795 + 6409842 * 2 ^ 59
def prefixEnd_6409842 : Nat := 4983230072969 + 3 ^ 40 * 6409842 * 2
def baseEnd_6409842 : Nat := 1097109955125538565798893

theorem tailTrace_6409842 : CollatzResearch.WordTrace tailWord_6409842 prefixEnd_6409842 1097109955125538565798893 := by
  unfold tailWord_6409842
  simp only [CollatzResearch.WordTrace]
  refine ⟨58446536011061155676021945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155857429362829748469391853 58446536011061155676021945)
  ·
    refine ⟨43834902008295866757016459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58446536011061155676021945 43834902008295866757016459)
    ·
      refine ⟨65752353012443800135524689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43834902008295866757016459 65752353012443800135524689)
      ·
        refine ⟨49314264759332850101643517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65752353012443800135524689 49314264759332850101643517)
        ·
          refine ⟨18492849284749818788116319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49314264759332850101643517 18492849284749818788116319)
          ·
            refine ⟨27739273927124728182174479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18492849284749818788116319 27739273927124728182174479)
            ·
              refine ⟨41608910890687092273261719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27739273927124728182174479 41608910890687092273261719)
              ·
                refine ⟨62413366336030638409892579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41608910890687092273261719 62413366336030638409892579)
                ·
                  refine ⟨93620049504045957614838869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62413366336030638409892579 93620049504045957614838869)
                  ·
                    refine ⟨1097109955125538565798893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93620049504045957614838869 1097109955125538565798893)
                    ·
                      rfl

theorem cell23_6409842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_6409842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409842 prefixEnd_6409842 := by exact prefixLift 6409842
  have htrace : WordTrace (prefixWord ++ tailWord_6409842) baseStart_6409842 baseEnd_6409842 := by
    simpa [prefixWord, tailWord_6409842, baseEnd_6409842] using wordTrace_append hprefix tailTrace_6409842
  have hstable : (prefixWord ++ tailWord_6409842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409842).length < 2 ^ (prefixWord ++ tailWord_6409842).sum := by decide
  have hdescent : baseEnd_6409842 < baseStart_6409842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409852 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_6409852 : Nat := 118140960795 + 6409852 * 2 ^ 59
def prefixEnd_6409852 : Nat := 4983230072969 + 3 ^ 40 * 6409852 * 2
def baseEnd_6409852 : Nat := 3291335000183160658271633

theorem tailTrace_6409852 : CollatzResearch.WordTrace tailWord_6409852 prefixEnd_6409852 3291335000183160658271633 := by
  unfold tailWord_6409852
  simp only [CollatzResearch.WordTrace]
  refine ⟨116893254387104197205975905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155857672516138929607967873 116893254387104197205975905)
  ·
    refine ⟨87669940790328147904481929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116893254387104197205975905 87669940790328147904481929)
    ·
      refine ⟨65752455592746110928361447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87669940790328147904481929 65752455592746110928361447)
      ·
        refine ⟨98628683389119166392542171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65752455592746110928361447 98628683389119166392542171)
        ·
          refine ⟨147943025083678749588813257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98628683389119166392542171 147943025083678749588813257)
          ·
            refine ⟨110957268812759062191609943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147943025083678749588813257 110957268812759062191609943)
            ·
              refine ⟨166435903219138593287414915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110957268812759062191609943 166435903219138593287414915)
              ·
                refine ⟨249653854828707889931122373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166435903219138593287414915 249653854828707889931122373)
                ·
                  refine ⟨46810097780382729362085445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249653854828707889931122373 46810097780382729362085445)
                  ·
                    refine ⟨8776893333821761755391021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46810097780382729362085445 8776893333821761755391021)
                    ·
                      refine ⟨3291335000183160658271633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8776893333821761755391021 3291335000183160658271633)
                      ·
                        rfl

theorem cell23_6409852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_6409852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409852 prefixEnd_6409852 := by exact prefixLift 6409852
  have htrace : WordTrace (prefixWord ++ tailWord_6409852) baseStart_6409852 baseEnd_6409852 := by
    simpa [prefixWord, tailWord_6409852, baseEnd_6409852] using wordTrace_append hprefix tailTrace_6409852
  have hstable : (prefixWord ++ tailWord_6409852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409852).length < 2 ^ (prefixWord ++ tailWord_6409852).sum := by decide
  have hdescent : baseEnd_6409852 < baseStart_6409852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409866 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_6409866 : Nat := 118140960795 + 6409866 * 2 ^ 59
def prefixEnd_6409866 : Nat := 4983230072969 + 3 ^ 40 * 6409866 * 2
def baseEnd_6409866 : Nat := 3291342188912323603496569

theorem tailTrace_6409866 : CollatzResearch.WordTrace tailWord_6409866 prefixEnd_6409866 3291342188912323603496569 := by
  unfold tailWord_6409866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58446754849039418700740363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155858012930771783201974301 58446754849039418700740363)
  ·
    refine ⟨87670132273559128051110545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58446754849039418700740363 87670132273559128051110545)
    ·
      refine ⟨65752599205169346038332909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87670132273559128051110545 65752599205169346038332909)
      ·
        refine ⟨24657224701938504764374841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65752599205169346038332909 24657224701938504764374841)
        ·
          refine ⟨18492918526453878573281131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24657224701938504764374841 18492918526453878573281131)
          ·
            refine ⟨27739377789680817859921697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18492918526453878573281131 27739377789680817859921697)
            ·
              refine ⟨20804533342260613394941273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27739377789680817859921697 20804533342260613394941273)
              ·
                refine ⟨15603400006695460046205955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20804533342260613394941273 15603400006695460046205955)
                ·
                  refine ⟨23405100010043190069308933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15603400006695460046205955 23405100010043190069308933)
                  ·
                    refine ⟨4388456251883098137995425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23405100010043190069308933 4388456251883098137995425)
                    ·
                      refine ⟨3291342188912323603496569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388456251883098137995425 3291342188912323603496569)
                      ·
                        rfl

theorem cell23_6409866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_6409866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409866 prefixEnd_6409866 := by exact prefixLift 6409866
  have htrace : WordTrace (prefixWord ++ tailWord_6409866) baseStart_6409866 baseEnd_6409866 := by
    simpa [prefixWord, tailWord_6409866, baseEnd_6409866] using wordTrace_append hprefix tailTrace_6409866
  have hstable : (prefixWord ++ tailWord_6409866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409866).length < 2 ^ (prefixWord ++ tailWord_6409866).sum := by decide
  have hdescent : baseEnd_6409866 < baseStart_6409866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409870 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6409870 : Nat := 118140960795 + 6409870 * 2 ^ 59
def prefixEnd_6409870 : Nat := 4983230072969 + 3 ^ 40 * 6409870 * 2
def baseEnd_6409870 : Nat := 3291344242834941587846551

theorem tailTrace_6409870 : CollatzResearch.WordTrace tailWord_6409870 prefixEnd_6409870 3291344242834941587846551 := by
  unfold tailWord_6409870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29223395661017897935763383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155858110192095455657404709 29223395661017897935763383)
  ·
    refine ⟨43835093491526846903645075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29223395661017897935763383 43835093491526846903645075)
    ·
      refine ⟨65752640237290270355467613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43835093491526846903645075 65752640237290270355467613)
      ·
        refine ⟨24657240088983851383300355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65752640237290270355467613 24657240088983851383300355)
        ·
          refine ⟨36985860133475777074950533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24657240088983851383300355 36985860133475777074950533)
          ·
            refine ⟨6934848775026708201553225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36985860133475777074950533 6934848775026708201553225)
            ·
              refine ⟨5201136581270031151164919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6934848775026708201553225 5201136581270031151164919)
              ·
                refine ⟨7801704871905046726747379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201136581270031151164919 7801704871905046726747379)
                ·
                  refine ⟨11702557307857570090121069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7801704871905046726747379 11702557307857570090121069)
                  ·
                    refine ⟨4388458990446588783795401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11702557307857570090121069 4388458990446588783795401)
                    ·
                      refine ⟨3291344242834941587846551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388458990446588783795401 3291344242834941587846551)
                      ·
                        rfl

theorem cell23_6409870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6409870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409870 prefixEnd_6409870 := by exact prefixLift 6409870
  have htrace : WordTrace (prefixWord ++ tailWord_6409870) baseStart_6409870 baseEnd_6409870 := by
    simpa [prefixWord, tailWord_6409870, baseEnd_6409870] using wordTrace_append hprefix tailTrace_6409870
  have hstable : (prefixWord ++ tailWord_6409870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409870).length < 2 ^ (prefixWord ++ tailWord_6409870).sum := by decide
  have hdescent : baseEnd_6409870 < baseStart_6409870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409889 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 7]
def baseStart_6409889 : Nat := 118140960795 + 6409889 * 2 ^ 59
def prefixEnd_6409889 : Nat := 4983230072969 + 3 ^ 40 * 6409889 * 2
def baseEnd_6409889 : Nat := 365705999885264112612107

theorem tailTrace_6409889 : CollatzResearch.WordTrace tailWord_6409889 prefixEnd_6409889 365705999885264112612107 := by
  unfold tailWord_6409889
  simp only [CollatzResearch.WordTrace]
  refine ⟨233787858275074349731048721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155858572183382899820699147 233787858275074349731048721)
  ·
    refine ⟨175340893706305762298286541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233787858275074349731048721 175340893706305762298286541)
    ·
      refine ⟨65752835139864660861857453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175340893706305762298286541 65752835139864660861857453)
      ·
        refine ⟨24657313177449247823196545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65752835139864660861857453 24657313177449247823196545)
        ·
          refine ⟨18492984883086935867397409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24657313177449247823196545 18492984883086935867397409)
          ·
            refine ⟨13869738662315201900548057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18492984883086935867397409 13869738662315201900548057)
            ·
              refine ⟨10402303996736401425411043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13869738662315201900548057 10402303996736401425411043)
              ·
                refine ⟨15603455995104602138116565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10402303996736401425411043 15603455995104602138116565)
                ·
                  refine ⟨365705999885264112612107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15603455995104602138116565 365705999885264112612107)
                  ·
                    rfl

theorem cell23_6409889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 7].length) (baseStart_6409889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409889 prefixEnd_6409889 := by exact prefixLift 6409889
  have htrace : WordTrace (prefixWord ++ tailWord_6409889) baseStart_6409889 baseEnd_6409889 := by
    simpa [prefixWord, tailWord_6409889, baseEnd_6409889] using wordTrace_append hprefix tailTrace_6409889
  have hstable : (prefixWord ++ tailWord_6409889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409889).length < 2 ^ (prefixWord ++ tailWord_6409889).sum := by decide
  have hdescent : baseEnd_6409889 < baseStart_6409889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6409952 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6409952 : Nat := 118140960795 + 6409952 * 2 ^ 59
def prefixEnd_6409952 : Nat := 4983230072969 + 3 ^ 40 * 6409952 * 2
def baseEnd_6409952 : Nat := 3291386348248610267021173

theorem tailTrace_6409952 : CollatzResearch.WordTrace tailWord_6409952 prefixEnd_6409952 3291386348248610267021173 := by
  unfold tailWord_6409952
  simp only [CollatzResearch.WordTrace]
  refine ⟨116895078036923055745296055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155860104049230740993728073 116895078036923055745296055)
  ·
    refine ⟨175342617055384583617944083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116895078036923055745296055 175342617055384583617944083)
    ·
      refine ⟨263013925583076875426916125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175342617055384583617944083 263013925583076875426916125)
      ·
        refine ⟨98630222093653828285093547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263013925583076875426916125 98630222093653828285093547)
        ·
          refine ⟨147945333140480742427640321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98630222093653828285093547 147945333140480742427640321)
          ·
            refine ⟨110958999855360556820730241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147945333140480742427640321 110958999855360556820730241)
            ·
              refine ⟨83219249891520417615547681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110958999855360556820730241 83219249891520417615547681)
              ·
                refine ⟨62414437418640313211660761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83219249891520417615547681 62414437418640313211660761)
                ·
                  refine ⟨46810828063980234908745571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62414437418640313211660761 46810828063980234908745571)
                  ·
                    refine ⟨70216242095970352363118357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46810828063980234908745571 70216242095970352363118357)
                    ·
                      refine ⟨3291386348248610267021173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70216242095970352363118357 3291386348248610267021173)
                      ·
                        rfl

theorem cell23_6409952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6409952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6409952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6409952 prefixEnd_6409952 := by exact prefixLift 6409952
  have htrace : WordTrace (prefixWord ++ tailWord_6409952) baseStart_6409952 baseEnd_6409952 := by
    simpa [prefixWord, tailWord_6409952, baseEnd_6409952] using wordTrace_append hprefix tailTrace_6409952
  have hstable : (prefixWord ++ tailWord_6409952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6409952).length < 2 ^ (prefixWord ++ tailWord_6409952).sum := by decide
  have hdescent : baseEnd_6409952 < baseStart_6409952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6409952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410016 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6410016 : Nat := 118140960795 + 6410016 * 2 ^ 59
def prefixEnd_6410016 : Nat := 4983230072969 + 3 ^ 40 * 6410016 * 2
def baseEnd_6410016 : Nat := 3291419211010498016620879

theorem tailTrace_6410016 : CollatzResearch.WordTrace tailWord_6410016 prefixEnd_6410016 3291419211010498016620879 := by
  unfold tailWord_6410016
  simp only [CollatzResearch.WordTrace]
  refine ⟨116896245172807125210460951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155861660230409500280614601 116896245172807125210460951)
  ·
    refine ⟨175344367759210687815691427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116896245172807125210460951 175344367759210687815691427)
    ·
      refine ⟨263016551638816031723537141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175344367759210687815691427 263016551638816031723537141)
      ·
        refine ⟨24657801716139002974081607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263016551638816031723537141 24657801716139002974081607)
        ·
          refine ⟨36986702574208504461122411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24657801716139002974081607 36986702574208504461122411)
          ·
            refine ⟨55480053861312756691683617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36986702574208504461122411 55480053861312756691683617)
            ·
              refine ⟨41610040395984567518762713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55480053861312756691683617 41610040395984567518762713)
              ·
                refine ⟨31207530296988425639072035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41610040395984567518762713 31207530296988425639072035)
                ·
                  refine ⟨46811295445482638458608053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31207530296988425639072035 46811295445482638458608053)
                  ·
                    refine ⟨4388558948013997355494505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46811295445482638458608053 4388558948013997355494505)
                    ·
                      refine ⟨3291419211010498016620879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388558948013997355494505 3291419211010498016620879)
                      ·
                        rfl

theorem cell23_6410016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6410016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410016 prefixEnd_6410016 := by exact prefixLift 6410016
  have htrace : WordTrace (prefixWord ++ tailWord_6410016) baseStart_6410016 baseEnd_6410016 := by
    simpa [prefixWord, tailWord_6410016, baseEnd_6410016] using wordTrace_append hprefix tailTrace_6410016
  have hstable : (prefixWord ++ tailWord_6410016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410016).length < 2 ^ (prefixWord ++ tailWord_6410016).sum := by decide
  have hdescent : baseEnd_6410016 < baseStart_6410016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410033 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 2, 3, 2]
def baseStart_6410033 : Nat := 118140960795 + 6410033 * 2 ^ 59
def prefixEnd_6410033 : Nat := 4983230072969 + 3 ^ 40 * 6410033 * 2
def baseEnd_6410033 : Nat := 3291427940181624450108301

theorem tailTrace_6410033 : CollatzResearch.WordTrace tailWord_6410033 prefixEnd_6410033 3291427940181624450108301 := by
  unfold tailWord_6410033
  simp only [CollatzResearch.WordTrace]
  refine ⟨233793110386552662324290753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155862073591035108216193835 233793110386552662324290753)
  ·
    refine ⟨175344832789914496743218065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233793110386552662324290753 175344832789914496743218065)
    ·
      refine ⟨131508624592435872557413549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175344832789914496743218065 131508624592435872557413549)
      ·
        refine ⟨49315734222163452209030081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131508624592435872557413549 49315734222163452209030081)
        ·
          refine ⟨36986800666622589156772561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49315734222163452209030081 36986800666622589156772561)
          ·
            refine ⟨27740100499966941867579421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36986800666622589156772561 27740100499966941867579421)
            ·
              refine ⟨10402537687487603200342283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27740100499966941867579421 10402537687487603200342283)
              ·
                refine ⟨15603806531231404800513425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10402537687487603200342283 15603806531231404800513425)
                ·
                  refine ⟨11702854898423553600385069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15603806531231404800513425 11702854898423553600385069)
                  ·
                    refine ⟨4388570586908832600144401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11702854898423553600385069 4388570586908832600144401)
                    ·
                      refine ⟨3291427940181624450108301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388570586908832600144401 3291427940181624450108301)
                      ·
                        rfl

theorem cell23_6410033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_6410033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410033 prefixEnd_6410033 := by exact prefixLift 6410033
  have htrace : WordTrace (prefixWord ++ tailWord_6410033) baseStart_6410033 baseEnd_6410033 := by
    simpa [prefixWord, tailWord_6410033, baseEnd_6410033] using wordTrace_append hprefix tailTrace_6410033
  have hstable : (prefixWord ++ tailWord_6410033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410033).length < 2 ^ (prefixWord ++ tailWord_6410033).sum := by decide
  have hdescent : baseEnd_6410033 < baseStart_6410033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410040 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 1, 1, 3]
def baseStart_6410040 : Nat := 118140960795 + 6410040 * 2 ^ 59
def prefixEnd_6410040 : Nat := 4983230072969 + 3 ^ 40 * 6410040 * 2
def baseEnd_6410040 : Nat := 3291431534546205922720769

theorem tailTrace_6410040 : CollatzResearch.WordTrace tailWord_6410040 prefixEnd_6410040 3291431534546205922720769 := by
  unfold tailWord_6410040
  simp only [CollatzResearch.WordTrace]
  refine ⟨116896682848763651259897787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155862243798351535013197049 116896682848763651259897787)
  ·
    refine ⟨175345024273145476889846681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116896682848763651259897787 175345024273145476889846681)
    ·
      refine ⟨131508768204859107667385011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175345024273145476889846681 131508768204859107667385011)
      ·
        refine ⟨197263152307288661501077517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131508768204859107667385011 197263152307288661501077517)
        ·
          refine ⟨73973682115233248062904069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197263152307288661501077517 73973682115233248062904069)
          ·
            refine ⟨13870065396606234011794513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73973682115233248062904069 13870065396606234011794513)
            ·
              refine ⟨10402549047454675508845885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13870065396606234011794513 10402549047454675508845885)
              ·
                refine ⟨3900955892795503315817207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10402549047454675508845885 3900955892795503315817207)
                ·
                  refine ⟨5851433839193254973725811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900955892795503315817207 5851433839193254973725811)
                  ·
                    refine ⟨8777150758789882460588717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5851433839193254973725811 8777150758789882460588717)
                    ·
                      refine ⟨3291431534546205922720769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8777150758789882460588717 3291431534546205922720769)
                      ·
                        rfl

theorem cell23_6410040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_6410040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410040 prefixEnd_6410040 := by exact prefixLift 6410040
  have htrace : WordTrace (prefixWord ++ tailWord_6410040) baseStart_6410040 baseEnd_6410040 := by
    simpa [prefixWord, tailWord_6410040, baseEnd_6410040] using wordTrace_append hprefix tailTrace_6410040
  have hstable : (prefixWord ++ tailWord_6410040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410040).length < 2 ^ (prefixWord ++ tailWord_6410040).sum := by decide
  have hdescent : baseEnd_6410040 < baseStart_6410040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410056 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 4, 4]
def baseStart_6410056 : Nat := 118140960795 + 6410056 * 2 ^ 59
def prefixEnd_6410056 : Nat := 4983230072969 + 3 ^ 40 * 6410056 * 2
def baseEnd_6410056 : Nat := 1097146583412225953373565

theorem tailTrace_6410056 : CollatzResearch.WordTrace tailWord_6410056 prefixEnd_6410056 1097146583412225953373565 := by
  unfold tailWord_6410056
  simp only [CollatzResearch.WordTrace]
  refine ⟨116896974632734668626189011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155862632843646224834918681 116896974632734668626189011)
  ·
    refine ⟨175345461949102002939283517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116896974632734668626189011 175345461949102002939283517)
    ·
      refine ⟨65754548230913251102231319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175345461949102002939283517 65754548230913251102231319)
      ·
        refine ⟨98631822346369876653346979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65754548230913251102231319 98631822346369876653346979)
        ·
          refine ⟨147947733519554814980020469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98631822346369876653346979 147947733519554814980020469)
          ·
            refine ⟨13870100017458263904376919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147947733519554814980020469 13870100017458263904376919)
            ·
              refine ⟨20805150026187395856565379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13870100017458263904376919 20805150026187395856565379)
              ·
                refine ⟨31207725039281093784848069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20805150026187395856565379 31207725039281093784848069)
                ·
                  refine ⟨5851448444865205084659013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31207725039281093784848069 5851448444865205084659013)
                  ·
                    refine ⟨1097146583412225953373565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851448444865205084659013 1097146583412225953373565)
                    ·
                      rfl

theorem cell23_6410056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_6410056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410056 prefixEnd_6410056 := by exact prefixLift 6410056
  have htrace : WordTrace (prefixWord ++ tailWord_6410056) baseStart_6410056 baseEnd_6410056 := by
    simpa [prefixWord, tailWord_6410056, baseEnd_6410056] using wordTrace_append hprefix tailTrace_6410056
  have hstable : (prefixWord ++ tailWord_6410056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410056).length < 2 ^ (prefixWord ++ tailWord_6410056).sum := by decide
  have hdescent : baseEnd_6410056 < baseStart_6410056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410066 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6410066 : Nat := 118140960795 + 6410066 * 2 ^ 59
def prefixEnd_6410066 : Nat := 4983230072969 + 3 ^ 40 * 6410066 * 2
def baseEnd_6410066 : Nat := 3291444885043222820995649

theorem tailTrace_6410066 : CollatzResearch.WordTrace tailWord_6410066 prefixEnd_6410066 3291444885043222820995649 := by
  unfold tailWord_6410066
  simp only [CollatzResearch.WordTrace]
  refine ⟨58448578498858277240060513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155862875996955405973494701 58448578498858277240060513)
  ·
    refine ⟨43836433874143707930045385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58448578498858277240060513 43836433874143707930045385)
    ·
      refine ⟨32877325405607780947534039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43836433874143707930045385 32877325405607780947534039)
      ·
        refine ⟨49315988108411671421301059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32877325405607780947534039 49315988108411671421301059)
        ·
          refine ⟨73973982162617507131951589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49315988108411671421301059 73973982162617507131951589)
          ·
            refine ⟨13870121655490782587240923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73973982162617507131951589 13870121655490782587240923)
            ·
              refine ⟨20805182483236173880861385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13870121655490782587240923 20805182483236173880861385)
              ·
                refine ⟨15603886862427130410646039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20805182483236173880861385 15603886862427130410646039)
                ·
                  refine ⟨23405830293640695615969059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15603886862427130410646039 23405830293640695615969059)
                  ·
                    refine ⟨35108745440461043423953589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23405830293640695615969059 35108745440461043423953589)
                    ·
                      refine ⟨3291444885043222820995649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35108745440461043423953589 3291444885043222820995649)
                      ·
                        rfl

theorem cell23_6410066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6410066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410066 prefixEnd_6410066 := by exact prefixLift 6410066
  have htrace : WordTrace (prefixWord ++ tailWord_6410066) baseStart_6410066 baseEnd_6410066 := by
    simpa [prefixWord, tailWord_6410066, baseEnd_6410066] using wordTrace_append hprefix tailTrace_6410066
  have hstable : (prefixWord ++ tailWord_6410066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410066).length < 2 ^ (prefixWord ++ tailWord_6410066).sum := by decide
  have hdescent : baseEnd_6410066 < baseStart_6410066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410073 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 2, 4]
def baseStart_6410073 : Nat := 118140960795 + 6410073 * 2 ^ 59
def prefixEnd_6410073 : Nat := 4983230072969 + 3 ^ 40 * 6410073 * 2
def baseEnd_6410073 : Nat := 1097149493135934764536039

theorem tailTrace_6410073 : CollatzResearch.WordTrace tailWord_6410073 prefixEnd_6410073 1097149493135934764536039 := by
  unfold tailWord_6410073
  simp only [CollatzResearch.WordTrace]
  refine ⟨233794569306407749155746873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155863046204271832770497915 233794569306407749155746873)
  ·
    refine ⟨175345926979805811866810155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233794569306407749155746873 175345926979805811866810155)
    ·
      refine ⟨263018890469708717800215233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175345926979805811866810155 263018890469708717800215233)
      ·
        refine ⟨197264167852281538350161425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263018890469708717800215233 197264167852281538350161425)
        ·
          refine ⟨147948125889211153762621069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197264167852281538350161425 147948125889211153762621069)
          ·
            refine ⟨55480547208454182660982901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147948125889211153762621069 55480547208454182660982901)
            ·
              refine ⟨5201301300792579624467147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55480547208454182660982901 5201301300792579624467147)
              ·
                refine ⟨7801951951188869436700721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201301300792579624467147 7801951951188869436700721)
                ·
                  refine ⟨5851463963391652077525541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7801951951188869436700721 5851463963391652077525541)
                  ·
                    refine ⟨1097149493135934764536039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851463963391652077525541 1097149493135934764536039)
                    ·
                      rfl

theorem cell23_6410073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 4].length) (baseStart_6410073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410073 prefixEnd_6410073 := by exact prefixLift 6410073
  have htrace : WordTrace (prefixWord ++ tailWord_6410073) baseStart_6410073 baseEnd_6410073 := by
    simpa [prefixWord, tailWord_6410073, baseEnd_6410073] using wordTrace_append hprefix tailTrace_6410073
  have hstable : (prefixWord ++ tailWord_6410073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410073).length < 2 ^ (prefixWord ++ tailWord_6410073).sum := by decide
  have hdescent : baseEnd_6410073 < baseStart_6410073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410109 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_6410109 : Nat := 118140960795 + 6410109 * 2 ^ 59
def prefixEnd_6410109 : Nat := 4983230072969 + 3 ^ 40 * 6410109 * 2
def baseEnd_6410109 : Nat := 3291466964711366152757951

theorem tailTrace_6410109 : CollatzResearch.WordTrace tailWord_6410109 prefixEnd_6410109 3291466964711366152757951 := by
  unfold tailWord_6410109
  simp only [CollatzResearch.WordTrace]
  refine ⟨233795882334277327304057381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155863921556184884869371587 233795882334277327304057381)
  ·
    refine ⟨43836727937676998869510759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233795882334277327304057381 43836727937676998869510759)
    ·
      refine ⟨65755091906515498304266139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43836727937676998869510759 65755091906515498304266139)
      ·
        refine ⟨98632637859773247456399209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65755091906515498304266139 98632637859773247456399209)
        ·
          refine ⟨73974478394829935592299407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98632637859773247456399209 73974478394829935592299407)
          ·
            refine ⟨110961717592244903388449111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73974478394829935592299407 110961717592244903388449111)
            ·
              refine ⟨166442576388367355082673667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110961717592244903388449111 166442576388367355082673667)
              ·
                refine ⟨249663864582551032624010501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166442576388367355082673667 249663864582551032624010501)
                ·
                  refine ⟨46811974609228318617001969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249663864582551032624010501 46811974609228318617001969)
                  ·
                    refine ⟨35108980956921238962751477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46811974609228318617001969 35108980956921238962751477)
                    ·
                      refine ⟨3291466964711366152757951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35108980956921238962751477 3291466964711366152757951)
                      ·
                        rfl

theorem cell23_6410109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_6410109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410109 prefixEnd_6410109 := by exact prefixLift 6410109
  have htrace : WordTrace (prefixWord ++ tailWord_6410109) baseStart_6410109 baseEnd_6410109 := by
    simpa [prefixWord, tailWord_6410109, baseEnd_6410109] using wordTrace_append hprefix tailTrace_6410109
  have hstable : (prefixWord ++ tailWord_6410109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410109).length < 2 ^ (prefixWord ++ tailWord_6410109).sum := by decide
  have hdescent : baseEnd_6410109 < baseStart_6410109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410129 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_6410129 : Nat := 118140960795 + 6410129 * 2 ^ 59
def prefixEnd_6410129 : Nat := 4983230072969 + 3 ^ 40 * 6410129 * 2
def baseEnd_6410129 : Nat := 1097159078108152024835953

theorem tailTrace_6410129 : CollatzResearch.WordTrace tailWord_6410129 prefixEnd_6410129 1097159078108152024835953 := by
  unfold tailWord_6410129
  simp only [CollatzResearch.WordTrace]
  refine ⟨233796611794204870719785441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155864407862803247146523627 233796611794204870719785441)
  ·
    refine ⟨175347458845653653039839081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233796611794204870719785441 175347458845653653039839081)
    ·
      refine ⟨131510594134240239779879311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175347458845653653039839081 131510594134240239779879311)
      ·
        refine ⟨197265891201360359669818967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131510594134240239779879311 197265891201360359669818967)
        ·
          refine ⟨295898836802040539504728451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197265891201360359669818967 295898836802040539504728451)
          ·
            refine ⟨443848255203060809257092677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295898836802040539504728451 443848255203060809257092677)
            ·
              refine ⟨83221547850573901735704877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443848255203060809257092677 83221547850573901735704877)
              ·
                refine ⟨31208080443965213150889329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83221547850573901735704877 31208080443965213150889329)
                ·
                  refine ⟨23406060332973909863166997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31208080443965213150889329 23406060332973909863166997)
                  ·
                    refine ⟨1097159078108152024835953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23406060332973909863166997 1097159078108152024835953)
                    ·
                      rfl

theorem cell23_6410129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_6410129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410129 prefixEnd_6410129 := by exact prefixLift 6410129
  have htrace : WordTrace (prefixWord ++ tailWord_6410129) baseStart_6410129 baseEnd_6410129 := by
    simpa [prefixWord, tailWord_6410129, baseEnd_6410129] using wordTrace_append hprefix tailTrace_6410129
  have hstable : (prefixWord ++ tailWord_6410129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410129).length < 2 ^ (prefixWord ++ tailWord_6410129).sum := by decide
  have hdescent : baseEnd_6410129 < baseStart_6410129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410140 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6410140 : Nat := 118140960795 + 6410140 * 2 ^ 59
def prefixEnd_6410140 : Nat := 4983230072969 + 3 ^ 40 * 6410140 * 2
def baseEnd_6410140 : Nat := 3291482882611655531470309

theorem tailTrace_6410140 : CollatzResearch.WordTrace tailWord_6410140 prefixEnd_6410140 3291482882611655531470309 := by
  unfold tailWord_6410140
  simp only [CollatzResearch.WordTrace]
  refine ⟨116898506498582509799217937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155864675331443346398957249 116898506498582509799217937)
  ·
    refine ⟨87673879873936882349413453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116898506498582509799217937 87673879873936882349413453)
    ·
      refine ⟨32877704952726330881030045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87673879873936882349413453 32877704952726330881030045)
      ·
        refine ⟨12329139357272374080386267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32877704952726330881030045 12329139357272374080386267)
        ·
          refine ⟨18493709035908561120579401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12329139357272374080386267 18493709035908561120579401)
          ·
            refine ⟨13870281776931420840434551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18493709035908561120579401 13870281776931420840434551)
            ·
              refine ⟨20805422665397131260651827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13870281776931420840434551 20805422665397131260651827)
              ·
                refine ⟨31208133998095696890977741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20805422665397131260651827 31208133998095696890977741)
                ·
                  refine ⟨11703050249285886334116653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31208133998095696890977741 11703050249285886334116653)
                  ·
                    refine ⟨4388643843482207375293745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11703050249285886334116653 4388643843482207375293745)
                    ·
                      refine ⟨3291482882611655531470309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388643843482207375293745 3291482882611655531470309)
                      ·
                        rfl

theorem cell23_6410140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6410140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410140 prefixEnd_6410140 := by exact prefixLift 6410140
  have htrace : WordTrace (prefixWord ++ tailWord_6410140) baseStart_6410140 baseEnd_6410140 := by
    simpa [prefixWord, tailWord_6410140, baseEnd_6410140] using wordTrace_append hprefix tailTrace_6410140
  have hstable : (prefixWord ++ tailWord_6410140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410140).length < 2 ^ (prefixWord ++ tailWord_6410140).sum := by decide
  have hdescent : baseEnd_6410140 < baseStart_6410140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410153 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 4, 2, 2]
def baseStart_6410153 : Nat := 118140960795 + 6410153 * 2 ^ 59
def prefixEnd_6410153 : Nat := 4983230072969 + 3 ^ 40 * 6410153 * 2
def baseEnd_6410153 : Nat := 3291489557860163980607749

theorem tailTrace_6410153 : CollatzResearch.WordTrace tailWord_6410153 prefixEnd_6410153 3291489557860163980607749 := by
  unfold tailWord_6410153
  simp only [CollatzResearch.WordTrace]
  refine ⟨233797487146117922818659113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155864991430745281879106075 233797487146117922818659113)
  ·
    refine ⟨175348115359588442113994335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233797487146117922818659113 175348115359588442113994335)
    ·
      refine ⟨263022173039382663170991503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175348115359588442113994335 263022173039382663170991503)
      ·
        refine ⟨394533259559073994756487255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263022173039382663170991503 394533259559073994756487255)
        ·
          refine ⟨591799889338610992134730883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394533259559073994756487255 591799889338610992134730883)
          ·
            refine ⟨887699834007916488202096325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591799889338610992134730883 887699834007916488202096325)
            ·
              refine ⟨166443718876484341537893061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 887699834007916488202096325 166443718876484341537893061)
              ·
                refine ⟨31208197289340814038354949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166443718876484341537893061 31208197289340814038354949)
                ·
                  refine ⟨5851536991751402632191553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31208197289340814038354949 5851536991751402632191553)
                  ·
                    refine ⟨4388652743813551974143665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5851536991751402632191553 4388652743813551974143665)
                    ·
                      refine ⟨3291489557860163980607749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388652743813551974143665 3291489557860163980607749)
                      ·
                        rfl

theorem cell23_6410153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 2, 2].length) (baseStart_6410153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410153 prefixEnd_6410153 := by exact prefixLift 6410153
  have htrace : WordTrace (prefixWord ++ tailWord_6410153) baseStart_6410153 baseEnd_6410153 := by
    simpa [prefixWord, tailWord_6410153, baseEnd_6410153] using wordTrace_append hprefix tailTrace_6410153
  have hstable : (prefixWord ++ tailWord_6410153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410153).length < 2 ^ (prefixWord ++ tailWord_6410153).sum := by decide
  have hdescent : baseEnd_6410153 < baseStart_6410153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410164 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6410164 : Nat := 118140960795 + 6410164 * 2 ^ 59
def prefixEnd_6410164 : Nat := 4983230072969 + 3 ^ 40 * 6410164 * 2
def baseEnd_6410164 : Nat := 3291495206147363437570199

theorem tailTrace_6410164 : CollatzResearch.WordTrace tailWord_6410164 prefixEnd_6410164 3291495206147363437570199 := by
  unfold tailWord_6410164
  simp only [CollatzResearch.WordTrace]
  refine ⟨116898944174539035848654773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155865258899385381131539697 116898944174539035848654773)
  ·
    refine ⟨10959276016363034610811385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116898944174539035848654773 10959276016363034610811385)
    ·
      refine ⟨8219457012272275958108539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10959276016363034610811385 8219457012272275958108539)
      ·
        refine ⟨12329185518408413937162809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8219457012272275958108539 12329185518408413937162809)
        ·
          refine ⟨9246889138806310452872107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12329185518408413937162809 9246889138806310452872107)
          ·
            refine ⟨13870333708209465679308161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9246889138806310452872107 13870333708209465679308161)
            ·
              refine ⟨10402750281157099259481121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13870333708209465679308161 10402750281157099259481121)
              ·
                refine ⟨7802062710867824444610841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10402750281157099259481121 7802062710867824444610841)
                ·
                  refine ⟨5851547033150868333458131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7802062710867824444610841 5851547033150868333458131)
                  ·
                    refine ⟨8777320549726302500187197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5851547033150868333458131 8777320549726302500187197)
                    ·
                      refine ⟨3291495206147363437570199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8777320549726302500187197 3291495206147363437570199)
                      ·
                        rfl

theorem cell23_6410164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6410164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410164 prefixEnd_6410164 := by exact prefixLift 6410164
  have htrace : WordTrace (prefixWord ++ tailWord_6410164) baseStart_6410164 baseEnd_6410164 := by
    simpa [prefixWord, tailWord_6410164, baseEnd_6410164] using wordTrace_append hprefix tailTrace_6410164
  have hstable : (prefixWord ++ tailWord_6410164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410164).length < 2 ^ (prefixWord ++ tailWord_6410164).sum := by decide
  have hdescent : baseEnd_6410164 < baseStart_6410164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410186 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_6410186 : Nat := 118140960795 + 6410186 * 2 ^ 59
def prefixEnd_6410186 : Nat := 4983230072969 + 3 ^ 40 * 6410186 * 2
def baseEnd_6410186 : Nat := 3291506502721762351495097

theorem tailTrace_6410186 : CollatzResearch.WordTrace tailWord_6410186 prefixEnd_6410186 3291506502721762351495097 := by
  unfold tailWord_6410186
  simp only [CollatzResearch.WordTrace]
  refine ⟨58449672688749592363652603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155865793836665579636406941 58449672688749592363652603)
  ·
    refine ⟨87674509033124388545478905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58449672688749592363652603 87674509033124388545478905)
    ·
      refine ⟨65755881774843291409109179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87674509033124388545478905 65755881774843291409109179)
      ·
        refine ⟨98633822662264937113663769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65755881774843291409109179 98633822662264937113663769)
        ·
          refine ⟨73975366996698702835247827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98633822662264937113663769 73975366996698702835247827)
          ·
            refine ⟨110963050495048054252871741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73975366996698702835247827 110963050495048054252871741)
            ·
              refine ⟨41611143935643020344826903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110963050495048054252871741 41611143935643020344826903)
              ·
                refine ⟨62416715903464530517240355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41611143935643020344826903 62416715903464530517240355)
                ·
                  refine ⟨93625073855196795775860533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62416715903464530517240355 93625073855196795775860533)
                  ·
                    refine ⟨8777350673924699603986925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93625073855196795775860533 8777350673924699603986925)
                    ·
                      refine ⟨3291506502721762351495097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8777350673924699603986925 3291506502721762351495097)
                      ·
                        rfl

theorem cell23_6410186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_6410186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410186 prefixEnd_6410186 := by exact prefixLift 6410186
  have htrace : WordTrace (prefixWord ++ tailWord_6410186) baseStart_6410186 baseEnd_6410186 := by
    simpa [prefixWord, tailWord_6410186, baseEnd_6410186] using wordTrace_append hprefix tailTrace_6410186
  have hstable : (prefixWord ++ tailWord_6410186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410186).length < 2 ^ (prefixWord ++ tailWord_6410186).sum := by decide
  have hdescent : baseEnd_6410186 < baseStart_6410186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410219 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 10]
def baseStart_6410219 : Nat := 118140960795 + 6410219 * 2 ^ 59
def prefixEnd_6410219 : Nat := 4983230072969 + 3 ^ 40 * 6410219 * 2
def baseEnd_6410219 : Nat := 1097174482527786907460815

theorem tailTrace_6410219 : CollatzResearch.WordTrace tailWord_6410219 prefixEnd_6410219 1097174482527786907460815 := by
  unfold tailWord_6410219
  simp only [CollatzResearch.WordTrace]
  refine ⟨233799894363878816090561711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155866596242585877393707807 233799894363878816090561711)
  ·
    refine ⟨350699841545818224135842567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233799894363878816090561711 350699841545818224135842567)
    ·
      refine ⟨526049762318727336203763851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350699841545818224135842567 526049762318727336203763851)
      ·
        refine ⟨789074643478091004305645777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526049762318727336203763851 789074643478091004305645777)
        ·
          refine ⟨591805982608568253229234333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789074643478091004305645777 591805982608568253229234333)
          ·
            refine ⟨221927243478213094960962875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591805982608568253229234333 221927243478213094960962875)
            ·
              refine ⟨332890865217319642441444313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221927243478213094960962875 332890865217319642441444313)
              ·
                refine ⟨249668148912989731831083235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332890865217319642441444313 249668148912989731831083235)
                ·
                  refine ⟨374502223369484597746624853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249668148912989731831083235 374502223369484597746624853)
                  ·
                    refine ⟨1097174482527786907460815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 374502223369484597746624853 1097174482527786907460815)
                    ·
                      rfl

theorem cell23_6410219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_6410219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410219 prefixEnd_6410219 := by exact prefixLift 6410219
  have htrace : WordTrace (prefixWord ++ tailWord_6410219) baseStart_6410219 baseEnd_6410219 := by
    simpa [prefixWord, tailWord_6410219, baseEnd_6410219] using wordTrace_append hprefix tailTrace_6410219
  have hstable : (prefixWord ++ tailWord_6410219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410219).length < 2 ^ (prefixWord ++ tailWord_6410219).sum := by decide
  have hdescent : baseEnd_6410219 < baseStart_6410219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410221 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6410221 : Nat := 118140960795 + 6410221 * 2 ^ 59
def prefixEnd_6410221 : Nat := 4983230072969 + 3 ^ 40 * 6410221 * 2
def baseEnd_6410221 : Nat := 3291524474544669714557437

theorem tailTrace_6410221 : CollatzResearch.WordTrace tailWord_6410221 prefixEnd_6410221 3291524474544669714557437 := by
  unfold tailWord_6410221
  simp only [CollatzResearch.WordTrace]
  refine ⟨233799967309871570432134517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155866644873247713621423011 233799967309871570432134517)
  ·
    refine ⟨21918746935300459728012611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233799967309871570432134517 21918746935300459728012611)
    ·
      refine ⟨32878120402950689592018917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21918746935300459728012611 32878120402950689592018917)
      ·
        refine ⟨6164647575553254298503547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32878120402950689592018917 6164647575553254298503547)
        ·
          refine ⟨9246971363329881447755321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6164647575553254298503547 9246971363329881447755321)
          ·
            refine ⟨6935228522497411085816491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9246971363329881447755321 6935228522497411085816491)
            ·
              refine ⟨10402842783746116628724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6935228522497411085816491 10402842783746116628724737)
              ·
                refine ⟨7802132087809587471543553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10402842783746116628724737 7802132087809587471543553)
                ·
                  refine ⟨5851599065857190603657665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7802132087809587471543553 5851599065857190603657665)
                  ·
                    refine ⟨4388699299392892952743249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5851599065857190603657665 4388699299392892952743249)
                    ·
                      refine ⟨3291524474544669714557437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388699299392892952743249 3291524474544669714557437)
                      ·
                        rfl

theorem cell23_6410221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6410221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410221 prefixEnd_6410221 := by exact prefixLift 6410221
  have htrace : WordTrace (prefixWord ++ tailWord_6410221) baseStart_6410221 baseEnd_6410221 := by
    simpa [prefixWord, tailWord_6410221, baseEnd_6410221] using wordTrace_append hprefix tailTrace_6410221
  have hstable : (prefixWord ++ tailWord_6410221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410221).length < 2 ^ (prefixWord ++ tailWord_6410221).sum := by decide
  have hdescent : baseEnd_6410221 < baseStart_6410221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410266 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_6410266 : Nat := 118140960795 + 6410266 * 2 ^ 59
def prefixEnd_6410266 : Nat := 4983230072969 + 3 ^ 40 * 6410266 * 2
def baseEnd_6410266 : Nat := 365727509019346893166081

theorem tailTrace_6410266 : CollatzResearch.WordTrace tailWord_6410266 prefixEnd_6410266 365727509019346893166081 := by
  unfold tailWord_6410266
  simp only [CollatzResearch.WordTrace]
  refine ⟨58450402148677135779380663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155867739063139028745015101 58450402148677135779380663)
  ·
    refine ⟨87675603223015703669070995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58450402148677135779380663 87675603223015703669070995)
    ·
      refine ⟨131513404834523555503606493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87675603223015703669070995 131513404834523555503606493)
      ·
        refine ⟨49317526812946333313852435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131513404834523555503606493 49317526812946333313852435)
        ·
          refine ⟨73976290219419499970778653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49317526812946333313852435 73976290219419499970778653)
          ·
            refine ⟨27741108832282312489041995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73976290219419499970778653 27741108832282312489041995)
            ·
              refine ⟨41611663248423468733562993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27741108832282312489041995 41611663248423468733562993)
              ·
                refine ⟨31208747436317601550172245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41611663248423468733562993 31208747436317601550172245)
                ·
                  refine ⟨365727509019346893166081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31208747436317601550172245 365727509019346893166081)
                  ·
                    rfl

theorem cell23_6410266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_6410266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410266 prefixEnd_6410266 := by exact prefixLift 6410266
  have htrace : WordTrace (prefixWord ++ tailWord_6410266) baseStart_6410266 baseEnd_6410266 := by
    simpa [prefixWord, tailWord_6410266, baseEnd_6410266] using wordTrace_append hprefix tailTrace_6410266
  have hstable : (prefixWord ++ tailWord_6410266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410266).length < 2 ^ (prefixWord ++ tailWord_6410266).sum := by decide
  have hdescent : baseEnd_6410266 < baseStart_6410266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410303 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 3, 5, 2]
def baseStart_6410303 : Nat := 118140960795 + 6410303 * 2 ^ 59
def prefixEnd_6410303 : Nat := 4983230072969 + 3 ^ 40 * 6410303 * 2
def baseEnd_6410303 : Nat := 3291566579958338393732059

theorem tailTrace_6410303 : CollatzResearch.WordTrace tailWord_6410303 prefixEnd_6410303 3291566579958338393732059 := by
  unfold tailWord_6410303
  simp only [CollatzResearch.WordTrace]
  refine ⟨233802958095574498436619563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155868638730382998957746375 233802958095574498436619563)
  ·
    refine ⟨350704437143361747654929345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233802958095574498436619563 350704437143361747654929345)
    ·
      refine ⟨263028327857521310741197009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350704437143361747654929345 263028327857521310741197009)
      ·
        refine ⟨197271245893140983055897757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263028327857521310741197009 197271245893140983055897757)
        ·
          refine ⟨73976717209927868645961659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197271245893140983055897757 73976717209927868645961659)
          ·
            refine ⟨110965075814891802968942489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73976717209927868645961659 110965075814891802968942489)
            ·
              refine ⟨83223806861168852226706867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110965075814891802968942489 83223806861168852226706867)
              ·
                refine ⟨124835710291753278340060301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83223806861168852226706867 124835710291753278340060301)
                ·
                  refine ⟨46813391359407479377522613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124835710291753278340060301 46813391359407479377522613)
                  ·
                    refine ⟨4388755439944451191642745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46813391359407479377522613 4388755439944451191642745)
                    ·
                      refine ⟨3291566579958338393732059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388755439944451191642745 3291566579958338393732059)
                      ·
                        rfl

theorem cell23_6410303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_6410303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410303 prefixEnd_6410303 := by exact prefixLift 6410303
  have htrace : WordTrace (prefixWord ++ tailWord_6410303) baseStart_6410303 baseEnd_6410303 := by
    simpa [prefixWord, tailWord_6410303, baseEnd_6410303] using wordTrace_append hprefix tailTrace_6410303
  have hstable : (prefixWord ++ tailWord_6410303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410303).length < 2 ^ (prefixWord ++ tailWord_6410303).sum := by decide
  have hdescent : baseEnd_6410303 < baseStart_6410303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410330 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_6410330 : Nat := 118140960795 + 6410330 * 2 ^ 59
def prefixEnd_6410330 : Nat := 4983230072969 + 3 ^ 40 * 6410330 * 2
def baseEnd_6410330 : Nat := 1097193481312003262698145

theorem tailTrace_6410330 : CollatzResearch.WordTrace tailWord_6410330 prefixEnd_6410330 1097193481312003262698145 := by
  unfold tailWord_6410330
  simp only [CollatzResearch.WordTrace]
  refine ⟨58450985716619170511963111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155869295244317788031901629 58450985716619170511963111)
  ·
    refine ⟨87676478574928755767944667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58450985716619170511963111 87676478574928755767944667)
    ·
      refine ⟨131514717862393133651917001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87676478574928755767944667 131514717862393133651917001)
      ·
        refine ⟨98636038396794850238937751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131514717862393133651917001 98636038396794850238937751)
        ·
          refine ⟨147954057595192275358406627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98636038396794850238937751 147954057595192275358406627)
          ·
            refine ⟨221931086392788413037609941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147954057595192275358406627 221931086392788413037609941)
            ·
              refine ⟨5201509837330978430568983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 221931086392788413037609941 5201509837330978430568983)
              ·
                refine ⟨7802264755996467645853475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201509837330978430568983 7802264755996467645853475)
                ·
                  refine ⟨11703397133994701468780213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7802264755996467645853475 11703397133994701468780213)
                  ·
                    refine ⟨1097193481312003262698145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11703397133994701468780213 1097193481312003262698145)
                    ·
                      rfl

theorem cell23_6410330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_6410330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410330 prefixEnd_6410330 := by exact prefixLift 6410330
  have htrace : WordTrace (prefixWord ++ tailWord_6410330) baseStart_6410330 baseEnd_6410330 := by
    simpa [prefixWord, tailWord_6410330, baseEnd_6410330] using wordTrace_append hprefix tailTrace_6410330
  have hstable : (prefixWord ++ tailWord_6410330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410330).length < 2 ^ (prefixWord ++ tailWord_6410330).sum := by decide
  have hdescent : baseEnd_6410330 < baseStart_6410330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410334 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_6410334 : Nat := 118140960795 + 6410334 * 2 ^ 59
def prefixEnd_6410334 : Nat := 4983230072969 + 3 ^ 40 * 6410334 * 2
def baseEnd_6410334 : Nat := 365731388650958641382713

theorem tailTrace_6410334 : CollatzResearch.WordTrace tailWord_6410334 prefixEnd_6410334 365731388650958641382713 := by
  unfold tailWord_6410334
  simp only [CollatzResearch.WordTrace]
  refine ⟨29225511094807773841374757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155869392505641460487332037 29225511094807773841374757)
  ·
    refine ⟨5479783330276457595257767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29225511094807773841374757 5479783330276457595257767)
    ·
      refine ⟨8219674995414686392886651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5479783330276457595257767 8219674995414686392886651)
      ·
        refine ⟨12329512493122029589329977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8219674995414686392886651 12329512493122029589329977)
        ·
          refine ⟨9247134369841522191997483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12329512493122029589329977 9247134369841522191997483)
          ·
            refine ⟨13870701554762283287996225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9247134369841522191997483 13870701554762283287996225)
            ·
              refine ⟨10403026166071712465997169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13870701554762283287996225 10403026166071712465997169)
              ·
                refine ⟨7802269624553784349497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10403026166071712465997169 7802269624553784349497877)
                ·
                  refine ⟨365731388650958641382713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7802269624553784349497877 365731388650958641382713)
                  ·
                    rfl

theorem cell23_6410334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_6410334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410334 prefixEnd_6410334 := by exact prefixLift 6410334
  have htrace : WordTrace (prefixWord ++ tailWord_6410334) baseStart_6410334 baseEnd_6410334 := by
    simpa [prefixWord, tailWord_6410334, baseEnd_6410334] using wordTrace_append hprefix tailTrace_6410334
  have hstable : (prefixWord ++ tailWord_6410334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410334).length < 2 ^ (prefixWord ++ tailWord_6410334).sum := by decide
  have hdescent : baseEnd_6410334 < baseStart_6410334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410338 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6410338 : Nat := 118140960795 + 6410338 * 2 ^ 59
def prefixEnd_6410338 : Nat := 4983230072969 + 3 ^ 40 * 6410338 * 2
def baseEnd_6410338 : Nat := 1097194850593748585598133

theorem tailTrace_6410338 : CollatzResearch.WordTrace tailWord_6410338 prefixEnd_6410338 1097194850593748585598133 := by
  unfold tailWord_6410338
  simp only [CollatzResearch.WordTrace]
  refine ⟨58451058662611924853535917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155869489766965132942762445 58451058662611924853535917)
  ·
    refine ⟨21919146998479471820075969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58451058662611924853535917 21919146998479471820075969)
    ·
      refine ⟨16439360248859603865056977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21919146998479471820075969 16439360248859603865056977)
      ·
        refine ⟨12329520186644702898792733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16439360248859603865056977 12329520186644702898792733)
        ·
          refine ⟨4623570069991763587047275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12329520186644702898792733 4623570069991763587047275)
          ·
            refine ⟨6935355104987645380570913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623570069991763587047275 6935355104987645380570913)
            ·
              refine ⟨5201516328740734035428185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935355104987645380570913 5201516328740734035428185)
              ·
                refine ⟨3901137246555550526571139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5201516328740734035428185 3901137246555550526571139)
                ·
                  refine ⟨5851705869833325789856709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901137246555550526571139 5851705869833325789856709)
                  ·
                    refine ⟨1097194850593748585598133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851705869833325789856709 1097194850593748585598133)
                    ·
                      rfl

theorem cell23_6410338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6410338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410338 prefixEnd_6410338 := by exact prefixLift 6410338
  have htrace : WordTrace (prefixWord ++ tailWord_6410338) baseStart_6410338 baseEnd_6410338 := by
    simpa [prefixWord, tailWord_6410338, baseEnd_6410338] using wordTrace_append hprefix tailTrace_6410338
  have hstable : (prefixWord ++ tailWord_6410338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410338).length < 2 ^ (prefixWord ++ tailWord_6410338).sum := by decide
  have hdescent : baseEnd_6410338 < baseStart_6410338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410353 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_6410353 : Nat := 118140960795 + 6410353 * 2 ^ 59
def prefixEnd_6410353 : Nat := 4983230072969 + 3 ^ 40 * 6410353 * 2
def baseEnd_6410353 : Nat := 3291592253991063198106829

theorem tailTrace_6410353 : CollatzResearch.WordTrace tailWord_6410353 prefixEnd_6410353 3291592253991063198106829 := by
  unfold tailWord_6410353
  simp only [CollatzResearch.WordTrace]
  refine ⟨233804781745393356975939713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155869854496928904650626475 233804781745393356975939713)
  ·
    refine ⟨175353586309045017731954785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233804781745393356975939713 175353586309045017731954785)
    ·
      refine ⟨131515189731783763298966089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175353586309045017731954785 131515189731783763298966089)
      ·
        refine ⟨98636392298837822474224567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131515189731783763298966089 98636392298837822474224567)
        ·
          refine ⟨147954588448256733711336851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98636392298837822474224567 147954588448256733711336851)
          ·
            refine ⟨221931882672385100567005277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147954588448256733711336851 221931882672385100567005277)
            ·
              refine ⟨83224456002144412712626979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221931882672385100567005277 83224456002144412712626979)
              ·
                refine ⟨124836684003216619068940469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83224456002144412712626979 124836684003216619068940469)
                ·
                  refine ⟨11703439125301558037713169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124836684003216619068940469 11703439125301558037713169)
                  ·
                    refine ⟨8777579343976168528284877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11703439125301558037713169 8777579343976168528284877)
                    ·
                      refine ⟨3291592253991063198106829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8777579343976168528284877 3291592253991063198106829)
                      ·
                        rfl

theorem cell23_6410353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_6410353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410353 prefixEnd_6410353 := by exact prefixLift 6410353
  have htrace : WordTrace (prefixWord ++ tailWord_6410353) baseStart_6410353 baseEnd_6410353 := by
    simpa [prefixWord, tailWord_6410353, baseEnd_6410353] using wordTrace_append hprefix tailTrace_6410353
  have hstable : (prefixWord ++ tailWord_6410353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410353).length < 2 ^ (prefixWord ++ tailWord_6410353).sum := by decide
  have hdescent : baseEnd_6410353 < baseStart_6410353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410384 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 1, 2, 2]
def baseStart_6410384 : Nat := 118140960795 + 6410384 * 2 ^ 59
def prefixEnd_6410384 : Nat := 4983230072969 + 3 ^ 40 * 6410384 * 2
def baseEnd_6410384 : Nat := 3291608171891352576819187

theorem tailTrace_6410384 : CollatzResearch.WordTrace tailWord_6410384 prefixEnd_6410384 3291608171891352576819187 := by
  unfold tailWord_6410384
  simp only [CollatzResearch.WordTrace]
  refine ⟨116902956204140524635159103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155870608272187366180212137 116902956204140524635159103)
  ·
    refine ⟨175354434306210786952738655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116902956204140524635159103 175354434306210786952738655)
    ·
      refine ⟨263031651459316180429107983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175354434306210786952738655 263031651459316180429107983)
      ·
        refine ⟨394547477188974270643661975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263031651459316180429107983 394547477188974270643661975)
        ·
          refine ⟨591821215783461405965492963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394547477188974270643661975 591821215783461405965492963)
          ·
            refine ⟨887731823675192108948239445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591821215783461405965492963 887731823675192108948239445)
            ·
              refine ⟨10403107308693657526737181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 887731823675192108948239445 10403107308693657526737181)
              ·
                refine ⟨3901165240760121572526443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10403107308693657526737181 3901165240760121572526443)
                ·
                  refine ⟨5851747861140182358789665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901165240760121572526443 5851747861140182358789665)
                  ·
                    refine ⟨4388810895855136769092249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5851747861140182358789665 4388810895855136769092249)
                    ·
                      refine ⟨3291608171891352576819187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388810895855136769092249 3291608171891352576819187)
                      ·
                        rfl

theorem cell23_6410384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 2, 2].length) (baseStart_6410384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410384 prefixEnd_6410384 := by exact prefixLift 6410384
  have htrace : WordTrace (prefixWord ++ tailWord_6410384) baseStart_6410384 baseEnd_6410384 := by
    simpa [prefixWord, tailWord_6410384, baseEnd_6410384] using wordTrace_append hprefix tailTrace_6410384
  have hstable : (prefixWord ++ tailWord_6410384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410384).length < 2 ^ (prefixWord ++ tailWord_6410384).sum := by decide
  have hdescent : baseEnd_6410384 < baseStart_6410384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410394 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_6410394 : Nat := 118140960795 + 6410394 * 2 ^ 59
def prefixEnd_6410394 : Nat := 4983230072969 + 3 ^ 40 * 6410394 * 2
def baseEnd_6410394 : Nat := 1097204435565965845898047

theorem tailTrace_6410394 : CollatzResearch.WordTrace tailWord_6410394 prefixEnd_6410394 1097204435565965845898047 := by
  unfold tailWord_6410394
  simp only [CollatzResearch.WordTrace]
  refine ⟨58451569284561205244545559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155870851425496547318788157 58451569284561205244545559)
  ·
    refine ⟨87677353926841807866818339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58451569284561205244545559 87677353926841807866818339)
    ·
      refine ⟨131516030890262711800227509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87677353926841807866818339 131516030890262711800227509)
      ·
        refine ⟨12329627895962129231271329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131516030890262711800227509 12329627895962129231271329)
        ·
          refine ⟨9247220921971596923453497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12329627895962129231271329 9247220921971596923453497)
          ·
            refine ⟨6935415691478697692590123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9247220921971596923453497 6935415691478697692590123)
            ·
              refine ⟨10403123537218046538885185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6935415691478697692590123 10403123537218046538885185)
              ·
                refine ⟨7802342652913534904163889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10403123537218046538885185 7802342652913534904163889)
                ·
                  refine ⟨5851756989685151178122917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7802342652913534904163889 5851756989685151178122917)
                  ·
                    refine ⟨1097204435565965845898047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851756989685151178122917 1097204435565965845898047)
                    ·
                      rfl

theorem cell23_6410394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_6410394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410394 prefixEnd_6410394 := by exact prefixLift 6410394
  have htrace : WordTrace (prefixWord ++ tailWord_6410394) baseStart_6410394 baseEnd_6410394 := by
    simpa [prefixWord, tailWord_6410394, baseEnd_6410394] using wordTrace_append hprefix tailTrace_6410394
  have hstable : (prefixWord ++ tailWord_6410394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410394).length < 2 ^ (prefixWord ++ tailWord_6410394).sum := by decide
  have hdescent : baseEnd_6410394 < baseStart_6410394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410427 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 1, 3, 2]
def baseStart_6410427 : Nat := 118140960795 + 6410427 * 2 ^ 59
def prefixEnd_6410427 : Nat := 4983230072969 + 3 ^ 40 * 6410427 * 2
def baseEnd_6410427 : Nat := 3291630251559495908581489

theorem tailTrace_6410427 : CollatzResearch.WordTrace tailWord_6410427 prefixEnd_6410427 3291630251559495908581489 := by
  unfold tailWord_6410427
  simp only [CollatzResearch.WordTrace]
  refine ⟨233807480747125267614133535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155871653831416845076089023 233807480747125267614133535)
  ·
    refine ⟨350711221120687901421200303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233807480747125267614133535 350711221120687901421200303)
    ·
      refine ⟨526066831681031852131800455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350711221120687901421200303 526066831681031852131800455)
      ·
        refine ⟨789100247521547778197700683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526066831681031852131800455 789100247521547778197700683)
        ·
          refine ⟨1183650371282321667296551025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789100247521547778197700683 1183650371282321667296551025)
          ·
            refine ⟨887737778461741250472413269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183650371282321667296551025 887737778461741250472413269)
            ·
              refine ⟨10403177091348530278973593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 887737778461741250472413269 10403177091348530278973593)
              ·
                refine ⟨7802382818511397709230195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10403177091348530278973593 7802382818511397709230195)
                ·
                  refine ⟨11703574227767096563845293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7802382818511397709230195 11703574227767096563845293)
                  ·
                    refine ⟨4388840335412661211441985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11703574227767096563845293 4388840335412661211441985)
                    ·
                      refine ⟨3291630251559495908581489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388840335412661211441985 3291630251559495908581489)
                      ·
                        rfl

theorem cell23_6410427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 3, 2].length) (baseStart_6410427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410427 prefixEnd_6410427 := by exact prefixLift 6410427
  have htrace : WordTrace (prefixWord ++ tailWord_6410427) baseStart_6410427 baseEnd_6410427 := by
    simpa [prefixWord, tailWord_6410427, baseEnd_6410427] using wordTrace_append hprefix tailTrace_6410427
  have hstable : (prefixWord ++ tailWord_6410427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410427).length < 2 ^ (prefixWord ++ tailWord_6410427).sum := by decide
  have hdescent : baseEnd_6410427 < baseStart_6410427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410440 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_6410440 : Nat := 118140960795 + 6410440 * 2 ^ 59
def prefixEnd_6410440 : Nat := 4983230072969 + 3 ^ 40 * 6410440 * 2
def baseEnd_6410440 : Nat := 3291636926808004357718929

theorem tailTrace_6410440 : CollatzResearch.WordTrace tailWord_6410440 prefixEnd_6410440 3291636926808004357718929 := by
  unfold tailWord_6410440
  simp only [CollatzResearch.WordTrace]
  refine ⟨116903977448039085417178387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155871969930718780556237849 116903977448039085417178387)
  ·
    refine ⟨175355966172058628125767581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116903977448039085417178387 175355966172058628125767581)
    ·
      refine ⟨65758487314521985547162843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175355966172058628125767581 65758487314521985547162843)
      ·
        refine ⟨98637730971782978320744265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65758487314521985547162843 98637730971782978320744265)
        ·
          refine ⟨73978298228837233740558199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98637730971782978320744265 73978298228837233740558199)
          ·
            refine ⟨110967447343255850610837299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73978298228837233740558199 110967447343255850610837299)
            ·
              refine ⟨166451171014883775916255949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110967447343255850610837299 166451171014883775916255949)
              ·
                refine ⟨62419189130581415968595981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166451171014883775916255949 62419189130581415968595981)
                ·
                  refine ⟨23407195923968030988223493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62419189130581415968595981 23407195923968030988223493)
                  ·
                    refine ⟨4388849235744005810291905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23407195923968030988223493 4388849235744005810291905)
                    ·
                      refine ⟨3291636926808004357718929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388849235744005810291905 3291636926808004357718929)
                      ·
                        rfl

theorem cell23_6410440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_6410440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410440 prefixEnd_6410440 := by exact prefixLift 6410440
  have htrace : WordTrace (prefixWord ++ tailWord_6410440) baseStart_6410440 baseEnd_6410440 := by
    simpa [prefixWord, tailWord_6410440, baseEnd_6410440] using wordTrace_append hprefix tailTrace_6410440
  have hstable : (prefixWord ++ tailWord_6410440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410440).length < 2 ^ (prefixWord ++ tailWord_6410440).sum := by decide
  have hdescent : baseEnd_6410440 < baseStart_6410440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410443 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5]
def baseStart_6410443 : Nat := 118140960795 + 6410443 * 2 ^ 59
def prefixEnd_6410443 : Nat := 4983230072969 + 3 ^ 40 * 6410443 * 2
def baseEnd_6410443 : Nat := 3291638467249967845981415

theorem tailTrace_6410443 : CollatzResearch.WordTrace tailWord_6410443 prefixEnd_6410443 3291638467249967845981415 := by
  unfold tailWord_6410443
  simp only [CollatzResearch.WordTrace]
  refine ⟨233808064315067302346715983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155872042876711534897810655 233808064315067302346715983)
  ·
    refine ⟨350712096472600953520073975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233808064315067302346715983 350712096472600953520073975)
    ·
      refine ⟨526068144708901430280110963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350712096472600953520073975 526068144708901430280110963)
      ·
        refine ⟨789102217063352145420166445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526068144708901430280110963 789102217063352145420166445)
        ·
          refine ⟨295913331398757054532562417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789102217063352145420166445 295913331398757054532562417)
          ·
            refine ⟨221934998549067790899421813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295913331398757054532562417 221934998549067790899421813)
            ·
              refine ⟨20806406113975105396820795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221934998549067790899421813 20806406113975105396820795)
              ·
                refine ⟨31209609170962658095231193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20806406113975105396820795 31209609170962658095231193)
                ·
                  refine ⟨23407206878221993571423395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31209609170962658095231193 23407206878221993571423395)
                  ·
                    refine ⟨35110810317332990357135093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23407206878221993571423395 35110810317332990357135093)
                    ·
                      refine ⟨3291638467249967845981415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35110810317332990357135093 3291638467249967845981415)
                      ·
                        rfl

theorem cell23_6410443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_6410443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410443 prefixEnd_6410443 := by exact prefixLift 6410443
  have htrace : WordTrace (prefixWord ++ tailWord_6410443) baseStart_6410443 baseEnd_6410443 := by
    simpa [prefixWord, tailWord_6410443, baseEnd_6410443] using wordTrace_append hprefix tailTrace_6410443
  have hstable : (prefixWord ++ tailWord_6410443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410443).length < 2 ^ (prefixWord ++ tailWord_6410443).sum := by decide
  have hdescent : baseEnd_6410443 < baseStart_6410443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410457 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 4, 2, 2]
def baseStart_6410457 : Nat := 118140960795 + 6410457 * 2 ^ 59
def prefixEnd_6410457 : Nat := 4983230072969 + 3 ^ 40 * 6410457 * 2
def baseEnd_6410457 : Nat := 3291645655979130791206351

theorem tailTrace_6410457 : CollatzResearch.WordTrace tailWord_6410457 prefixEnd_6410457 3291645655979130791206351 := by
  unfold tailWord_6410457
  simp only [CollatzResearch.WordTrace]
  refine ⟨233808574937016582737725625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155872383291344388491817083 233808574937016582737725625)
  ·
    refine ⟨175356431202762437053294219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233808574937016582737725625 175356431202762437053294219)
    ·
      refine ⟨263034646804143655579941329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175356431202762437053294219 263034646804143655579941329)
      ·
        refine ⟨197275985103107741684955997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263034646804143655579941329 197275985103107741684955997)
        ·
          refine ⟨73978494413665403131858499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197275985103107741684955997 73978494413665403131858499)
          ·
            refine ⟨110967741620498104697787749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73978494413665403131858499 110967741620498104697787749)
            ·
              refine ⟨20806451553843394630835203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110967741620498104697787749 20806451553843394630835203)
              ·
                refine ⟨31209677330765091946252805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20806451553843394630835203 31209677330765091946252805)
                ·
                  refine ⟨5851814499518454739922401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31209677330765091946252805 5851814499518454739922401)
                  ·
                    refine ⟨4388860874638841054941801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5851814499518454739922401 4388860874638841054941801)
                    ·
                      refine ⟨3291645655979130791206351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388860874638841054941801 3291645655979130791206351)
                      ·
                        rfl

theorem cell23_6410457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_6410457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410457 prefixEnd_6410457 := by exact prefixLift 6410457
  have htrace : WordTrace (prefixWord ++ tailWord_6410457) baseStart_6410457 baseEnd_6410457 := by
    simpa [prefixWord, tailWord_6410457, baseEnd_6410457] using wordTrace_append hprefix tailTrace_6410457
  have hstable : (prefixWord ++ tailWord_6410457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410457).length < 2 ^ (prefixWord ++ tailWord_6410457).sum := by decide
  have hdescent : baseEnd_6410457 < baseStart_6410457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410474 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_6410474 : Nat := 118140960795 + 6410474 * 2 ^ 59
def prefixEnd_6410474 : Nat := 4983230072969 + 3 ^ 40 * 6410474 * 2
def baseEnd_6410474 : Nat := 3291654385150257224693773

theorem tailTrace_6410474 : CollatzResearch.WordTrace tailWord_6410474 prefixEnd_6410474 3291654385150257224693773 := by
  unfold tailWord_6410474
  simp only [CollatzResearch.WordTrace]
  refine ⟨58452298744488748660273619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155872796651969996427396317 58452298744488748660273619)
  ·
    refine ⟨87678448116733122990410429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58452298744488748660273619 87678448116733122990410429)
    ·
      refine ⟨32879418043774921121403911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87678448116733122990410429 32879418043774921121403911)
      ·
        refine ⟨49319127065662381682105867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32879418043774921121403911 49319127065662381682105867)
        ·
          refine ⟨73978690598493572523158801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49319127065662381682105867 73978690598493572523158801)
          ·
            refine ⟨55484017948870179392369101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73978690598493572523158801 55484017948870179392369101)
            ·
              refine ⟨20806506730826317272138413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55484017948870179392369101 20806506730826317272138413)
              ·
                refine ⟨7802440024059868977051905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20806506730826317272138413 7802440024059868977051905)
                ·
                  refine ⟨5851830018044901732788929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7802440024059868977051905 5851830018044901732788929)
                  ·
                    refine ⟨4388872513533676299591697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5851830018044901732788929 4388872513533676299591697)
                    ·
                      refine ⟨3291654385150257224693773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4388872513533676299591697 3291654385150257224693773)
                      ·
                        rfl

theorem cell23_6410474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_6410474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410474 prefixEnd_6410474 := by exact prefixLift 6410474
  have htrace : WordTrace (prefixWord ++ tailWord_6410474) baseStart_6410474 baseEnd_6410474 := by
    simpa [prefixWord, tailWord_6410474, baseEnd_6410474] using wordTrace_append hprefix tailTrace_6410474
  have hstable : (prefixWord ++ tailWord_6410474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410474).length < 2 ^ (prefixWord ++ tailWord_6410474).sum := by decide
  have hdescent : baseEnd_6410474 < baseStart_6410474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410493 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_6410493 : Nat := 118140960795 + 6410493 * 2 ^ 59
def prefixEnd_6410493 : Nat := 4983230072969 + 3 ^ 40 * 6410493 * 2
def baseEnd_6410493 : Nat := 1097221380427564216785395

theorem tailTrace_6410493 : CollatzResearch.WordTrace tailWord_6410493 prefixEnd_6410493 1097221380427564216785395 := by
  unfold tailWord_6410493
  simp only [CollatzResearch.WordTrace]
  refine ⟨233809887964886160886036133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155873258643257440590690755 233809887964886160886036133)
  ·
    refine ⟨43839353993416155166131775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233809887964886160886036133 43839353993416155166131775)
    ·
      refine ⟨65759030990124232749197663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43839353993416155166131775 65759030990124232749197663)
      ·
        refine ⟨98638546485186349123796495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65759030990124232749197663 98638546485186349123796495)
        ·
          refine ⟨147957819727779523685694743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98638546485186349123796495 147957819727779523685694743)
          ·
            refine ⟨221936729591669285528542115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147957819727779523685694743 221936729591669285528542115)
            ·
              refine ⟨332905094387503928292813173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221936729591669285528542115 332905094387503928292813173)
              ·
                refine ⟨31209852598828493277451235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332905094387503928292813173 31209852598828493277451235)
                ·
                  refine ⟨46814778898242739916176853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31209852598828493277451235 46814778898242739916176853)
                  ·
                    refine ⟨1097221380427564216785395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46814778898242739916176853 1097221380427564216785395)
                    ·
                      rfl

theorem cell23_6410493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_6410493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410493 prefixEnd_6410493 := by exact prefixLift 6410493
  have htrace : WordTrace (prefixWord ++ tailWord_6410493) baseStart_6410493 baseEnd_6410493 := by
    simpa [prefixWord, tailWord_6410493, baseEnd_6410493] using wordTrace_append hprefix tailTrace_6410493
  have hstable : (prefixWord ++ tailWord_6410493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410493).length < 2 ^ (prefixWord ++ tailWord_6410493).sum := by decide
  have hdescent : baseEnd_6410493 < baseStart_6410493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410510 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_6410510 : Nat := 118140960795 + 6410510 * 2 ^ 59
def prefixEnd_6410510 : Nat := 4983230072969 + 3 ^ 40 * 6410510 * 2
def baseEnd_6410510 : Nat := 1097224290151273027947869

theorem tailTrace_6410510 : CollatzResearch.WordTrace tailWord_6410510 prefixEnd_6410510 1097224290151273027947869 := by
  unfold tailWord_6410510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29226313500728071598675623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155873672003883048526269989 29226313500728071598675623)
  ·
    refine ⟨43839470251092107398013435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29226313500728071598675623 43839470251092107398013435)
    ·
      refine ⟨65759205376638161097020153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43839470251092107398013435 65759205376638161097020153)
      ·
        refine ⟨49319404032478620822765115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65759205376638161097020153 49319404032478620822765115)
        ·
          refine ⟨73979106048717931234147673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49319404032478620822765115 73979106048717931234147673)
          ·
            refine ⟨55484329536538448425610755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73979106048717931234147673 55484329536538448425610755)
            ·
              refine ⟨83226494304807672638416133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55484329536538448425610755 83226494304807672638416133)
              ·
                refine ⟨15604967682151438619703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83226494304807672638416133 15604967682151438619703025)
                ·
                  refine ⟨11703725761613578964777269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15604967682151438619703025 11703725761613578964777269)
                  ·
                    refine ⟨1097224290151273027947869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11703725761613578964777269 1097224290151273027947869)
                    ·
                      rfl

theorem cell23_6410510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_6410510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410510 prefixEnd_6410510 := by exact prefixLift 6410510
  have htrace : WordTrace (prefixWord ++ tailWord_6410510) baseStart_6410510 baseEnd_6410510 := by
    simpa [prefixWord, tailWord_6410510, baseEnd_6410510] using wordTrace_append hprefix tailTrace_6410510
  have hstable : (prefixWord ++ tailWord_6410510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410510).length < 2 ^ (prefixWord ++ tailWord_6410510).sum := by decide
  have hdescent : baseEnd_6410510 < baseStart_6410510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410540 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_6410540 : Nat := 118140960795 + 6410540 * 2 ^ 59
def prefixEnd_6410540 : Nat := 4983230072969 + 3 ^ 40 * 6410540 * 2
def baseEnd_6410540 : Nat := 1097229424957817988822823

theorem tailTrace_6410540 : CollatzResearch.WordTrace tailWord_6410540 prefixEnd_6410540 1097229424957817988822823 := by
  unfold tailWord_6410540
  simp only [CollatzResearch.WordTrace]
  refine ⟨116905801097857943956498537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155874401463810591941998049 116905801097857943956498537)
  ·
    refine ⟨87679350823393457967373903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116905801097857943956498537 87679350823393457967373903)
    ·
      refine ⟨131519026235090186951060855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87679350823393457967373903 131519026235090186951060855)
      ·
        refine ⟨197278539352635280426591283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131519026235090186951060855 197278539352635280426591283)
        ·
          refine ⟨295917809028952920639886925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197278539352635280426591283 295917809028952920639886925)
          ·
            refine ⟨110969178385857345239957597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295917809028952920639886925 110969178385857345239957597)
            ·
              refine ⟨41613441894696504464984099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110969178385857345239957597 41613441894696504464984099)
              ·
                refine ⟨62420162842044756697476149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41613441894696504464984099 62420162842044756697476149)
                ·
                  refine ⟨5851890266441695940388389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62420162842044756697476149 5851890266441695940388389)
                  ·
                    refine ⟨1097229424957817988822823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851890266441695940388389 1097229424957817988822823)
                    ·
                      rfl

theorem cell23_6410540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_6410540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410540 prefixEnd_6410540 := by exact prefixLift 6410540
  have htrace : WordTrace (prefixWord ++ tailWord_6410540) baseStart_6410540 baseEnd_6410540 := by
    simpa [prefixWord, tailWord_6410540, baseEnd_6410540] using wordTrace_append hprefix tailTrace_6410540
  have hstable : (prefixWord ++ tailWord_6410540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410540).length < 2 ^ (prefixWord ++ tailWord_6410540).sum := by decide
  have hdescent : baseEnd_6410540 < baseStart_6410540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410660 : List Nat := [2, 3, 1, 2, 1, 1, 4, 9]
def baseStart_6410660 : Nat := 118140960795 + 6410660 * 2 ^ 59
def prefixEnd_6410660 : Nat := 4983230072969 + 3 ^ 40 * 6410660 * 2
def baseEnd_6410660 : Nat := 121916662687110870258071

theorem tailTrace_6410660 : CollatzResearch.WordTrace tailWord_6410660 prefixEnd_6410660 121916662687110870258071 := by
  unfold tailWord_6410660
  simp only [CollatzResearch.WordTrace]
  refine ⟨116907989477640574203682717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155877319303520765604910289 116907989477640574203682717)
  ·
    refine ⟨43840496054115215326381019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116907989477640574203682717 43840496054115215326381019)
    ·
      refine ⟨65760744081172822989571529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43840496054115215326381019 65760744081172822989571529)
      ·
        refine ⟨49320558060879617242178647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65760744081172822989571529 49320558060879617242178647)
        ·
          refine ⟨73980837091319425863267971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49320558060879617242178647 73980837091319425863267971)
          ·
            refine ⟨110971255636979138794901957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73980837091319425863267971 110971255636979138794901957)
            ·
              refine ⟨20807110431933588524044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110971255636979138794901957 20807110431933588524044117)
              ·
                refine ⟨121916662687110870258071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20807110431933588524044117 121916662687110870258071)
                ·
                  rfl

theorem cell23_6410660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 9].length) (baseStart_6410660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410660 prefixEnd_6410660 := by exact prefixLift 6410660
  have htrace : WordTrace (prefixWord ++ tailWord_6410660) baseStart_6410660 baseEnd_6410660 := by
    simpa [prefixWord, tailWord_6410660, baseEnd_6410660] using wordTrace_append hprefix tailTrace_6410660
  have hstable : (prefixWord ++ tailWord_6410660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410660).length < 2 ^ (prefixWord ++ tailWord_6410660).sum := by decide
  have hdescent : baseEnd_6410660 < baseStart_6410660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410664 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6410664 : Nat := 118140960795 + 6410664 * 2 ^ 59
def prefixEnd_6410664 : Nat := 4983230072969 + 3 ^ 40 * 6410664 * 2
def baseEnd_6410664 : Nat := 1097250648824870493772633

theorem tailTrace_6410664 : CollatzResearch.WordTrace tailWord_6410664 prefixEnd_6410664 1097250648824870493772633 := by
  unfold tailWord_6410664
  simp only [CollatzResearch.WordTrace]
  refine ⟨116908062423633328545255523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155877416564844438060340697 116908062423633328545255523)
  ·
    refine ⟨175362093635449992817883285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116908062423633328545255523 175362093635449992817883285)
    ·
      refine ⟨8220098139161718413338279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175362093635449992817883285 8220098139161718413338279)
      ·
        refine ⟨12330147208742577620007419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8220098139161718413338279 12330147208742577620007419)
        ·
          refine ⟨18495220813113866430011129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12330147208742577620007419 18495220813113866430011129)
          ·
            refine ⟨13871415609835399822508347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18495220813113866430011129 13871415609835399822508347)
            ·
              refine ⟨20807123414753099733762521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13871415609835399822508347 20807123414753099733762521)
              ·
                refine ⟨15605342561064824800321891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20807123414753099733762521 15605342561064824800321891)
                ·
                  refine ⟨23408013841597237200482837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15605342561064824800321891 23408013841597237200482837)
                  ·
                    refine ⟨1097250648824870493772633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23408013841597237200482837 1097250648824870493772633)
                    ·
                      rfl

theorem cell23_6410664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6410664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410664 prefixEnd_6410664 := by exact prefixLift 6410664
  have htrace : WordTrace (prefixWord ++ tailWord_6410664) baseStart_6410664 baseEnd_6410664 := by
    simpa [prefixWord, tailWord_6410664, baseEnd_6410664] using wordTrace_append hprefix tailTrace_6410664
  have hstable : (prefixWord ++ tailWord_6410664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410664).length < 2 ^ (prefixWord ++ tailWord_6410664).sum := by decide
  have hdescent : baseEnd_6410664 < baseStart_6410664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410677 : List Nat := [1, 3, 3, 2, 4, 10]
def baseStart_6410677 : Nat := 118140960795 + 6410677 * 2 ^ 59
def prefixEnd_6410677 : Nat := 4983230072969 + 3 ^ 40 * 6410677 * 2
def baseEnd_6410677 : Nat := 13546331776638353623273

theorem tailTrace_6410677 : CollatzResearch.WordTrace tailWord_6410677 prefixEnd_6410677 13546331776638353623273 := by
  unfold tailWord_6410677
  simp only [CollatzResearch.WordTrace]
  refine ⟨233816598996219560310734285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155877732664146373540489523 233816598996219560310734285)
  ·
    refine ⟨87681224623582335116525357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233816598996219560310734285 87681224623582335116525357)
    ·
      refine ⟨32880459233843375668697009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87681224623582335116525357 32880459233843375668697009)
      ·
        refine ⟨24660344425382531751522757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32880459233843375668697009 24660344425382531751522757)
        ·
          refine ⟨4623814579759224703410517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24660344425382531751522757 4623814579759224703410517)
          ·
            refine ⟨13546331776638353623273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4623814579759224703410517 13546331776638353623273)
            ·
              rfl

theorem cell23_6410677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 10].length) (baseStart_6410677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410677 prefixEnd_6410677 := by exact prefixLift 6410677
  have htrace : WordTrace (prefixWord ++ tailWord_6410677) baseStart_6410677 baseEnd_6410677 := by
    simpa [prefixWord, tailWord_6410677, baseEnd_6410677] using wordTrace_append hprefix tailTrace_6410677
  have hstable : (prefixWord ++ tailWord_6410677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410677).length < 2 ^ (prefixWord ++ tailWord_6410677).sum := by decide
  have hdescent : baseEnd_6410677 < baseStart_6410677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410714 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2]
def baseStart_6410714 : Nat := 118140960795 + 6410714 * 2 ^ 59
def prefixEnd_6410714 : Nat := 4983230072969 + 3 ^ 40 * 6410714 * 2
def baseEnd_6410714 : Nat := 3291777620507336285692669

theorem tailTrace_6410714 : CollatzResearch.WordTrace tailWord_6410714 prefixEnd_6410714 3291777620507336285692669 := by
  unfold tailWord_6410714
  simp only [CollatzResearch.WordTrace]
  refine ⟨58454487124271378907457799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155878632331390343753220797 58454487124271378907457799)
  ·
    refine ⟨87681730686407068361186699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58454487124271378907457799 87681730686407068361186699)
    ·
      refine ⟨131522596029610602541780049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87681730686407068361186699 131522596029610602541780049)
      ·
        refine ⟨98641947022207951906335037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131522596029610602541780049 98641947022207951906335037)
        ·
          refine ⟨36990730133327981964875639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98641947022207951906335037 36990730133327981964875639)
          ·
            refine ⟨55486095199991972947313459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36990730133327981964875639 55486095199991972947313459)
            ·
              refine ⟨83229142799987959420970189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55486095199991972947313459 83229142799987959420970189)
              ·
                refine ⟨31210928549995484782863821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83229142799987959420970189 31210928549995484782863821)
                ·
                  refine ⟨11704098206248306793573933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31210928549995484782863821 11704098206248306793573933)
                  ·
                    refine ⟨4389036827343115047590225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11704098206248306793573933 4389036827343115047590225)
                    ·
                      refine ⟨3291777620507336285692669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389036827343115047590225 3291777620507336285692669)
                      ·
                        rfl

theorem cell23_6410714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_6410714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410714 prefixEnd_6410714 := by exact prefixLift 6410714
  have htrace : WordTrace (prefixWord ++ tailWord_6410714) baseStart_6410714 baseEnd_6410714 := by
    simpa [prefixWord, tailWord_6410714, baseEnd_6410714] using wordTrace_append hprefix tailTrace_6410714
  have hstable : (prefixWord ++ tailWord_6410714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410714).length < 2 ^ (prefixWord ++ tailWord_6410714).sum := by decide
  have hdescent : baseEnd_6410714 < baseStart_6410714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410717 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6410717 : Nat := 118140960795 + 6410717 * 2 ^ 59
def prefixEnd_6410717 : Nat := 4983230072969 + 3 ^ 40 * 6410717 * 2
def baseEnd_6410717 : Nat := 3291779160949299773955155

theorem tailTrace_6410717 : CollatzResearch.WordTrace tailWord_6410717 prefixEnd_6410717 3291779160949299773955155 := by
  unfold tailWord_6410717
  simp only [CollatzResearch.WordTrace]
  refine ⟨233818057916074647142190405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155878705277383098094793603 233818057916074647142190405)
  ·
    refine ⟨43840885859263996339160701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233818057916074647142190405 43840885859263996339160701)
    ·
      refine ⟨16440332197223998627185263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43840885859263996339160701 16440332197223998627185263)
      ·
        refine ⟨24660498295835997940777895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16440332197223998627185263 24660498295835997940777895)
        ·
          refine ⟨36990747443753996911166843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24660498295835997940777895 36990747443753996911166843)
          ·
            refine ⟨55486121165630995366750265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36990747443753996911166843 55486121165630995366750265)
            ·
              refine ⟨41614590874223246525062699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55486121165630995366750265 41614590874223246525062699)
              ·
                refine ⟨62421886311334869787594049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41614590874223246525062699 62421886311334869787594049)
                ·
                  refine ⟨46816414733501152340695537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62421886311334869787594049 46816414733501152340695537)
                  ·
                    refine ⟨35112311050125864255521653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46816414733501152340695537 35112311050125864255521653)
                    ·
                      refine ⟨3291779160949299773955155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35112311050125864255521653 3291779160949299773955155)
                      ·
                        rfl

theorem cell23_6410717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6410717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410717 prefixEnd_6410717 := by exact prefixLift 6410717
  have htrace : WordTrace (prefixWord ++ tailWord_6410717) baseStart_6410717 baseEnd_6410717 := by
    simpa [prefixWord, tailWord_6410717, baseEnd_6410717] using wordTrace_append hprefix tailTrace_6410717
  have hstable : (prefixWord ++ tailWord_6410717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410717).length < 2 ^ (prefixWord ++ tailWord_6410717).sum := by decide
  have hdescent : baseEnd_6410717 < baseStart_6410717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410720 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_6410720 : Nat := 118140960795 + 6410720 * 2 ^ 59
def prefixEnd_6410720 : Nat := 4983230072969 + 3 ^ 40 * 6410720 * 2
def baseEnd_6410720 : Nat := 1097260233797087754072547

theorem tailTrace_6410720 : CollatzResearch.WordTrace tailWord_6410720 prefixEnd_6410720 1097260233797087754072547 := by
  unfold tailWord_6410720
  simp only [CollatzResearch.WordTrace]
  refine ⟨116909083667531889327274807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155878778223375852436366409 116909083667531889327274807)
  ·
    refine ⟨175363625501297833990912211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116909083667531889327274807 175363625501297833990912211)
    ·
      refine ⟨263045438251946750986368317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175363625501297833990912211 263045438251946750986368317)
      ·
        refine ⟨98642039344480031619888119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263045438251946750986368317 98642039344480031619888119)
        ·
          refine ⟨147963059016720047429832179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98642039344480031619888119 147963059016720047429832179)
          ·
            refine ⟨221944588525080071144748269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147963059016720047429832179 221944588525080071144748269)
            ·
              refine ⟨83229220696905026679280601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221944588525080071144748269 83229220696905026679280601)
              ·
                refine ⟨62421915522678770009460451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83229220696905026679280601 62421915522678770009460451)
                ·
                  refine ⟨93632873284018155014190677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62421915522678770009460451 93632873284018155014190677)
                  ·
                    refine ⟨1097260233797087754072547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93632873284018155014190677 1097260233797087754072547)
                    ·
                      rfl

theorem cell23_6410720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_6410720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410720 prefixEnd_6410720 := by exact prefixLift 6410720
  have htrace : WordTrace (prefixWord ++ tailWord_6410720) baseStart_6410720 baseEnd_6410720 := by
    simpa [prefixWord, tailWord_6410720, baseEnd_6410720] using wordTrace_append hprefix tailTrace_6410720
  have hstable : (prefixWord ++ tailWord_6410720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410720).length < 2 ^ (prefixWord ++ tailWord_6410720).sum := by decide
  have hdescent : baseEnd_6410720 < baseStart_6410720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410722 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6410722 : Nat := 118140960795 + 6410722 * 2 ^ 59
def prefixEnd_6410722 : Nat := 4983230072969 + 3 ^ 40 * 6410722 * 2
def baseEnd_6410722 : Nat := 3291781728352572254392633

theorem tailTrace_6410722 : CollatzResearch.WordTrace tailWord_6410722 prefixEnd_6410722 3291781728352572254392633 := by
  unfold tailWord_6410722
  simp only [CollatzResearch.WordTrace]
  refine ⟨58454560070264133249030605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155878826854037688664081613 58454560070264133249030605)
  ·
    refine ⟨21920460026349049968386477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58454560070264133249030605 21920460026349049968386477)
    ·
      refine ⟨8220172509880893738144929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21920460026349049968386477 8220172509880893738144929)
      ·
        refine ⟨6165129382410670303608697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8220172509880893738144929 6165129382410670303608697)
        ·
          refine ⟨4623847036808002727706523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6165129382410670303608697 4623847036808002727706523)
          ·
            refine ⟨6935770555212004091559785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623847036808002727706523 6935770555212004091559785)
            ·
              refine ⟨5201827916409003068669839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935770555212004091559785 5201827916409003068669839)
              ·
                refine ⟨7802741874613504603004759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201827916409003068669839 7802741874613504603004759)
                ·
                  refine ⟨11704112811920256904507139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7802741874613504603004759 11704112811920256904507139)
                  ·
                    refine ⟨17556169217880385356760709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11704112811920256904507139 17556169217880385356760709)
                    ·
                      refine ⟨3291781728352572254392633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17556169217880385356760709 3291781728352572254392633)
                      ·
                        rfl

theorem cell23_6410722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6410722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410722 prefixEnd_6410722 := by exact prefixLift 6410722
  have htrace : WordTrace (prefixWord ++ tailWord_6410722) baseStart_6410722 baseEnd_6410722 := by
    simpa [prefixWord, tailWord_6410722, baseEnd_6410722] using wordTrace_append hprefix tailTrace_6410722
  have hstable : (prefixWord ++ tailWord_6410722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410722).length < 2 ^ (prefixWord ++ tailWord_6410722).sum := by decide
  have hdescent : baseEnd_6410722 < baseStart_6410722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410725 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6410725 : Nat := 118140960795 + 6410725 * 2 ^ 59
def prefixEnd_6410725 : Nat := 4983230072969 + 3 ^ 40 * 6410725 * 2
def baseEnd_6410725 : Nat := 3291783268794535742655119

theorem tailTrace_6410725 : CollatzResearch.WordTrace tailWord_6410725 prefixEnd_6410725 3291783268794535742655119 := by
  unfold tailWord_6410725
  simp only [CollatzResearch.WordTrace]
  refine ⟨233818349700045664508481629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155878899800030443005654419 233818349700045664508481629)
  ·
    refine ⟨87681881137517124190680611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233818349700045664508481629 87681881137517124190680611)
    ·
      refine ⟨131522821706275686286020917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87681881137517124190680611 131522821706275686286020917)
      ·
        refine ⟨12330264534963345589314461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131522821706275686286020917 12330264534963345589314461)
        ·
          refine ⟨4623849200611254595992923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12330264534963345589314461 4623849200611254595992923)
          ·
            refine ⟨6935773800916881893989385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623849200611254595992923 6935773800916881893989385)
            ·
              refine ⟨5201830350687661420492039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935773800916881893989385 5201830350687661420492039)
              ·
                refine ⟨7802745526031492130738059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201830350687661420492039 7802745526031492130738059)
                ·
                  refine ⟨11704118289047238196107089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7802745526031492130738059 11704118289047238196107089)
                  ·
                    refine ⟨8778088716785428647080317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11704118289047238196107089 8778088716785428647080317)
                    ·
                      refine ⟨3291783268794535742655119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778088716785428647080317 3291783268794535742655119)
                      ·
                        rfl

theorem cell23_6410725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6410725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410725 prefixEnd_6410725 := by exact prefixLift 6410725
  have htrace : WordTrace (prefixWord ++ tailWord_6410725) baseStart_6410725 baseEnd_6410725 := by
    simpa [prefixWord, tailWord_6410725, baseEnd_6410725] using wordTrace_append hprefix tailTrace_6410725
  have hstable : (prefixWord ++ tailWord_6410725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410725).length < 2 ^ (prefixWord ++ tailWord_6410725).sum := by decide
  have hdescent : baseEnd_6410725 < baseStart_6410725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410757 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_6410757 : Nat := 118140960795 + 6410757 * 2 ^ 59
def prefixEnd_6410757 : Nat := 4983230072969 + 3 ^ 40 * 6410757 * 2
def baseEnd_6410757 : Nat := 3291799700175479617454971

theorem tailTrace_6410757 : CollatzResearch.WordTrace tailWord_6410757 prefixEnd_6410757 3291799700175479617454971 := by
  unfold tailWord_6410757
  simp only [CollatzResearch.WordTrace]
  refine ⟨233819516835929733973646525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155879677890619822649097683 233819516835929733973646525)
  ·
    refine ⟨87682318813473650240117447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233819516835929733973646525 87682318813473650240117447)
    ·
      refine ⟨131523478220210475360176171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87682318813473650240117447 131523478220210475360176171)
      ·
        refine ⟨197285217330315713040264257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131523478220210475360176171 197285217330315713040264257)
        ·
          refine ⟨147963912997736784780198193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197285217330315713040264257 147963912997736784780198193)
          ·
            refine ⟨110972934748302588585148645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147963912997736784780198193 110972934748302588585148645)
            ·
              refine ⟨20807425265306735359715371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110972934748302588585148645 20807425265306735359715371)
              ·
                refine ⟨31211137897960103039573057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20807425265306735359715371 31211137897960103039573057)
                ·
                  refine ⟨23408353423470077279679793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31211137897960103039573057 23408353423470077279679793)
                  ·
                    refine ⟨17556265067602557959759845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23408353423470077279679793 17556265067602557959759845)
                    ·
                      refine ⟨3291799700175479617454971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17556265067602557959759845 3291799700175479617454971)
                      ·
                        rfl

theorem cell23_6410757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_6410757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410757 prefixEnd_6410757 := by exact prefixLift 6410757
  have htrace : WordTrace (prefixWord ++ tailWord_6410757) baseStart_6410757 baseEnd_6410757 := by
    simpa [prefixWord, tailWord_6410757, baseEnd_6410757] using wordTrace_append hprefix tailTrace_6410757
  have hstable : (prefixWord ++ tailWord_6410757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410757).length < 2 ^ (prefixWord ++ tailWord_6410757).sum := by decide
  have hdescent : baseEnd_6410757 < baseStart_6410757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410765 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6410765 : Nat := 118140960795 + 6410765 * 2 ^ 59
def prefixEnd_6410765 : Nat := 4983230072969 + 3 ^ 40 * 6410765 * 2
def baseEnd_6410765 : Nat := 3291803808020715586154935

theorem tailTrace_6410765 : CollatzResearch.WordTrace tailWord_6410765 prefixEnd_6410765 3291803808020715586154935 := by
  unfold tailWord_6410765
  simp only [CollatzResearch.WordTrace]
  refine ⟨233819808619900751339937749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155879872413267167559958499 233819808619900751339937749)
  ·
    refine ⟨5480151764528923859529791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 233819808619900751339937749 5480151764528923859529791)
    ·
      refine ⟨8220227646793385789294687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5480151764528923859529791 8220227646793385789294687)
      ·
        refine ⟨12330341470190078683942031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8220227646793385789294687 12330341470190078683942031)
        ·
          refine ⟨18495512205285118025913047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12330341470190078683942031 18495512205285118025913047)
          ·
            refine ⟨27743268307927677038869571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18495512205285118025913047 27743268307927677038869571)
            ·
              refine ⟨41614902461891515558304357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27743268307927677038869571 41614902461891515558304357)
              ·
                refine ⟨7802794211604659167182067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41614902461891515558304357 7802794211604659167182067)
                ·
                  refine ⟨11704191317406988750773101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7802794211604659167182067 11704191317406988750773101)
                  ·
                    refine ⟨4389071744027620781539913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11704191317406988750773101 4389071744027620781539913)
                    ·
                      refine ⟨3291803808020715586154935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389071744027620781539913 3291803808020715586154935)
                      ·
                        rfl

theorem cell23_6410765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6410765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410765 prefixEnd_6410765 := by exact prefixLift 6410765
  have htrace : WordTrace (prefixWord ++ tailWord_6410765) baseStart_6410765 baseEnd_6410765 := by
    simpa [prefixWord, tailWord_6410765, baseEnd_6410765] using wordTrace_append hprefix tailTrace_6410765
  have hstable : (prefixWord ++ tailWord_6410765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410765).length < 2 ^ (prefixWord ++ tailWord_6410765).sum := by decide
  have hdescent : baseEnd_6410765 < baseStart_6410765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410807 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_6410807 : Nat := 118140960795 + 6410807 * 2 ^ 59
def prefixEnd_6410807 : Nat := 4983230072969 + 3 ^ 40 * 6410807 * 2
def baseEnd_6410807 : Nat := 3291825374208204421829741

theorem tailTrace_6410807 : CollatzResearch.WordTrace tailWord_6410807 prefixEnd_6410807 3291825374208204421829741 := by
  unfold tailWord_6410807
  simp only [CollatzResearch.WordTrace]
  refine ⟨233821340485748592512966675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155880893657165728341977783 233821340485748592512966675)
  ·
    refine ⟨350732010728622888769450013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233821340485748592512966675 350732010728622888769450013)
    ·
      refine ⟨131524504023233583288543755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350732010728622888769450013 131524504023233583288543755)
      ·
        refine ⟨197286756034850374932815633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131524504023233583288543755 197286756034850374932815633)
        ·
          refine ⟨147965067026137781199611725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197286756034850374932815633 147965067026137781199611725)
          ·
            refine ⟨55486900134801667949854397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147965067026137781199611725 55486900134801667949854397)
            ·
              refine ⟨20807587550550625481195399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55486900134801667949854397 20807587550550625481195399)
              ·
                refine ⟨31211381325825938221793099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20807587550550625481195399 31211381325825938221793099)
                ·
                  refine ⟨46817071988738907332689649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31211381325825938221793099 46817071988738907332689649)
                  ·
                    refine ⟨35112803991554180499517237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46817071988738907332689649 35112803991554180499517237)
                    ·
                      refine ⟨3291825374208204421829741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35112803991554180499517237 3291825374208204421829741)
                      ·
                        rfl

theorem cell23_6410807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_6410807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410807 prefixEnd_6410807 := by exact prefixLift 6410807
  have htrace : WordTrace (prefixWord ++ tailWord_6410807) baseStart_6410807 baseEnd_6410807 := by
    simpa [prefixWord, tailWord_6410807, baseEnd_6410807] using wordTrace_append hprefix tailTrace_6410807
  have hstable : (prefixWord ++ tailWord_6410807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410807).length < 2 ^ (prefixWord ++ tailWord_6410807).sum := by decide
  have hdescent : baseEnd_6410807 < baseStart_6410807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410882 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6410882 : Nat := 118140960795 + 6410882 * 2 ^ 59
def prefixEnd_6410882 : Nat := 4983230072969 + 3 ^ 40 * 6410882 * 2
def baseEnd_6410882 : Nat := 1097287961752430542797299

theorem tailTrace_6410882 : CollatzResearch.WordTrace tailWord_6410882 prefixEnd_6410882 1097287961752430542797299 := by
  unfold tailWord_6410882
  simp only [CollatzResearch.WordTrace]
  refine ⟨58456018990119220080486725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155882717306984586881297933 58456018990119220080486725)
  ·
    refine ⟨10960503560647353765091261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58456018990119220080486725 10960503560647353765091261)
    ·
      refine ⟨4110188835242757661909223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10960503560647353765091261 4110188835242757661909223)
      ·
        refine ⟨6165283252864136492863835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110188835242757661909223 6165283252864136492863835)
        ·
          refine ⟨9247924879296204739295753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165283252864136492863835 9247924879296204739295753)
          ·
            refine ⟨6935943659472153554471815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9247924879296204739295753 6935943659472153554471815)
            ·
              refine ⟨10403915489208230331707723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6935943659472153554471815 10403915489208230331707723)
              ·
                refine ⟨15605873233812345497561585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10403915489208230331707723 15605873233812345497561585)
                ·
                  refine ⟨11704404925359259123171189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15605873233812345497561585 11704404925359259123171189)
                  ·
                    refine ⟨1097287961752430542797299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11704404925359259123171189 1097287961752430542797299)
                    ·
                      rfl

theorem cell23_6410882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6410882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410882 prefixEnd_6410882 := by exact prefixLift 6410882
  have htrace : WordTrace (prefixWord ++ tailWord_6410882) baseStart_6410882 baseEnd_6410882 := by
    simpa [prefixWord, tailWord_6410882, baseEnd_6410882] using wordTrace_append hprefix tailTrace_6410882
  have hstable : (prefixWord ++ tailWord_6410882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410882).length < 2 ^ (prefixWord ++ tailWord_6410882).sum := by decide
  have hdescent : baseEnd_6410882 < baseStart_6410882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410907 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4]
def baseStart_6410907 : Nat := 118140960795 + 6410907 * 2 ^ 59
def prefixEnd_6410907 : Nat := 4983230072969 + 3 ^ 40 * 6410907 * 2
def baseEnd_6410907 : Nat := 3291876722273654030579281

theorem tailTrace_6410907 : CollatzResearch.WordTrace tailWord_6410907 prefixEnd_6410907 3291876722273654030579281 := by
  unfold tailWord_6410907
  simp only [CollatzResearch.WordTrace]
  refine ⟨233824987785386309591606975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155883325190257539727737983 233824987785386309591606975)
  ·
    refine ⟨350737481678079464387410463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233824987785386309591606975 350737481678079464387410463)
    ·
      refine ⟨526106222517119196581115695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350737481678079464387410463 526106222517119196581115695)
      ·
        refine ⟨789159333775678794871673543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526106222517119196581115695 789159333775678794871673543)
        ·
          refine ⟨1183739000663518192307510315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789159333775678794871673543 1183739000663518192307510315)
          ·
            refine ⟨1775608500995277288461265473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183739000663518192307510315 1775608500995277288461265473)
            ·
              refine ⟨1331706375746457966345949105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775608500995277288461265473 1331706375746457966345949105)
              ·
                refine ⟨998779781809843474759461829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331706375746457966345949105 998779781809843474759461829)
                ·
                  refine ⟨187271209089345651517399093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998779781809843474759461829 187271209089345651517399093)
                  ·
                    refine ⟨17556675852126154829756165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187271209089345651517399093 17556675852126154829756165)
                    ·
                      refine ⟨3291876722273654030579281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17556675852126154829756165 3291876722273654030579281)
                      ·
                        rfl

theorem cell23_6410907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_6410907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410907 prefixEnd_6410907 := by exact prefixLift 6410907
  have htrace : WordTrace (prefixWord ++ tailWord_6410907) baseStart_6410907 baseEnd_6410907 := by
    simpa [prefixWord, tailWord_6410907, baseEnd_6410907] using wordTrace_append hprefix tailTrace_6410907
  have hstable : (prefixWord ++ tailWord_6410907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410907).length < 2 ^ (prefixWord ++ tailWord_6410907).sum := by decide
  have hdescent : baseEnd_6410907 < baseStart_6410907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410941 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_6410941 : Nat := 118140960795 + 6410941 * 2 ^ 59
def prefixEnd_6410941 : Nat := 4983230072969 + 3 ^ 40 * 6410941 * 2
def baseEnd_6410941 : Nat := 3291894180615906897554125

theorem tailTrace_6410941 : CollatzResearch.WordTrace tailWord_6410941 prefixEnd_6410941 3291894180615906897554125 := by
  unfold tailWord_6410941
  simp only [CollatzResearch.WordTrace]
  refine ⟨233826227867263133398344677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155884151911508755598896451 233826227867263133398344677)
  ·
    refine ⟨43842417725111837512189627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233826227867263133398344677 43842417725111837512189627)
    ·
      refine ⟨65763626587667756268284441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43842417725111837512189627 65763626587667756268284441)
      ·
        refine ⟨49322719940750817201213331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65763626587667756268284441 49322719940750817201213331)
        ·
          refine ⟨73984079911126225801819997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49322719940750817201213331 73984079911126225801819997)
          ·
            refine ⟨27744029966672334675682499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73984079911126225801819997 27744029966672334675682499)
            ·
              refine ⟨41616044950008502013523749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27744029966672334675682499 41616044950008502013523749)
              ·
                refine ⟨7803008428126594127535703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41616044950008502013523749 7803008428126594127535703)
                ·
                  refine ⟨11704512642189891191303555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7803008428126594127535703 11704512642189891191303555)
                  ·
                    refine ⟨17556768963284836786955333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11704512642189891191303555 17556768963284836786955333)
                    ·
                      refine ⟨3291894180615906897554125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17556768963284836786955333 3291894180615906897554125)
                      ·
                        rfl

theorem cell23_6410941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_6410941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410941 prefixEnd_6410941 := by exact prefixLift 6410941
  have htrace : WordTrace (prefixWord ++ tailWord_6410941) baseStart_6410941 baseEnd_6410941 := by
    simpa [prefixWord, tailWord_6410941, baseEnd_6410941] using wordTrace_append hprefix tailTrace_6410941
  have hstable : (prefixWord ++ tailWord_6410941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410941).length < 2 ^ (prefixWord ++ tailWord_6410941).sum := by decide
  have hdescent : baseEnd_6410941 < baseStart_6410941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410961 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_6410961 : Nat := 118140960795 + 6410961 * 2 ^ 59
def prefixEnd_6410961 : Nat := 4983230072969 + 3 ^ 40 * 6410961 * 2
def baseEnd_6410961 : Nat := 3291904450228996819304033

theorem tailTrace_6410961 : CollatzResearch.WordTrace tailWord_6410961 prefixEnd_6410961 3291904450228996819304033 := by
  unfold tailWord_6410961
  simp only [CollatzResearch.WordTrace]
  refine ⟨233826957327190676814072737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155884638218127117876048491 233826957327190676814072737)
  ·
    refine ⟨175370217995393007610554553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233826957327190676814072737 175370217995393007610554553)
    ·
      refine ⟨131527663496544755707915915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175370217995393007610554553 131527663496544755707915915)
      ·
        refine ⟨197291495244817133561873873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131527663496544755707915915 197291495244817133561873873)
        ·
          refine ⟨147968621433612850171405405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197291495244817133561873873 147968621433612850171405405)
          ·
            refine ⟨55488233037604818814277027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147968621433612850171405405 55488233037604818814277027)
            ·
              refine ⟨83232349556407228221415541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55488233037604818814277027 83232349556407228221415541)
              ·
                refine ⟨7803032770913177645757707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83232349556407228221415541 7803032770913177645757707)
                ·
                  refine ⟨11704549156369766468636561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7803032770913177645757707 11704549156369766468636561)
                  ·
                    refine ⟨8778411867277324851477421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11704549156369766468636561 8778411867277324851477421)
                    ·
                      refine ⟨3291904450228996819304033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778411867277324851477421 3291904450228996819304033)
                      ·
                        rfl

theorem cell23_6410961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_6410961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410961 prefixEnd_6410961 := by exact prefixLift 6410961
  have htrace : WordTrace (prefixWord ++ tailWord_6410961) baseStart_6410961 baseEnd_6410961 := by
    simpa [prefixWord, tailWord_6410961, baseEnd_6410961] using wordTrace_append hprefix tailTrace_6410961
  have hstable : (prefixWord ++ tailWord_6410961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410961).length < 2 ^ (prefixWord ++ tailWord_6410961).sum := by decide
  have hdescent : baseEnd_6410961 < baseStart_6410961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6410975 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 3, 2, 2]
def baseStart_6410975 : Nat := 118140960795 + 6410975 * 2 ^ 59
def prefixEnd_6410975 : Nat := 4983230072969 + 3 ^ 40 * 6410975 * 2
def baseEnd_6410975 : Nat := 3291911638958159764528969

theorem tailTrace_6410975 : CollatzResearch.WordTrace tailWord_6410975 prefixEnd_6410975 3291911638958159764528969 := by
  unfold tailWord_6410975
  simp only [CollatzResearch.WordTrace]
  refine ⟨233827467949139957205082379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155884978632759971470054919 233827467949139957205082379)
  ·
    refine ⟨350741201923709935807623569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233827467949139957205082379 350741201923709935807623569)
    ·
      refine ⟨263055901442782451855717677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350741201923709935807623569 263055901442782451855717677)
      ·
        refine ⟨98645963041043419445894129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263055901442782451855717677 98645963041043419445894129)
        ·
          refine ⟨73984472280782564584420597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98645963041043419445894129 73984472280782564584420597)
          ·
            refine ⟨6936044276323365429789431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73984472280782564584420597 6936044276323365429789431)
            ·
              refine ⟨10404066414485048144684147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936044276323365429789431 10404066414485048144684147)
              ·
                refine ⟨15606099621727572217026221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10404066414485048144684147 15606099621727572217026221)
                ·
                  refine ⟨5852287358147839581384833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15606099621727572217026221 5852287358147839581384833)
                  ·
                    refine ⟨4389215518610879686038625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5852287358147839581384833 4389215518610879686038625)
                    ·
                      refine ⟨3291911638958159764528969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389215518610879686038625 3291911638958159764528969)
                      ·
                        rfl

theorem cell23_6410975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_6410975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6410975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6410975 prefixEnd_6410975 := by exact prefixLift 6410975
  have htrace : WordTrace (prefixWord ++ tailWord_6410975) baseStart_6410975 baseEnd_6410975 := by
    simpa [prefixWord, tailWord_6410975, baseEnd_6410975] using wordTrace_append hprefix tailTrace_6410975
  have hstable : (prefixWord ++ tailWord_6410975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6410975).length < 2 ^ (prefixWord ++ tailWord_6410975).sum := by decide
  have hdescent : baseEnd_6410975 < baseStart_6410975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6410975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411069 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6411069 : Nat := 118140960795 + 6411069 * 2 ^ 59
def prefixEnd_6411069 : Nat := 4983230072969 + 3 ^ 40 * 6411069 * 2
def baseEnd_6411069 : Nat := 3291959906139682396753537

theorem tailTrace_6411069 : CollatzResearch.WordTrace tailWord_6411069 prefixEnd_6411069 3291959906139682396753537 := by
  unfold tailWord_6411069
  simp only [CollatzResearch.WordTrace]
  refine ⟨233830896410799411259004261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155887264273866274172669507 233830896410799411259004261)
  ·
    refine ⟨43843293077024889611063299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233830896410799411259004261 43843293077024889611063299)
    ·
      refine ⟨65764939615537334416594949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43843293077024889611063299 65764939615537334416594949)
      ·
        refine ⟨12330926177913250203111553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65764939615537334416594949 12330926177913250203111553)
        ·
          refine ⟨9248194633434937652333665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12330926177913250203111553 9248194633434937652333665)
          ·
            refine ⟨6936145975076203239250249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9248194633434937652333665 6936145975076203239250249)
            ·
              refine ⟨5202109481307152429437687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6936145975076203239250249 5202109481307152429437687)
              ·
                refine ⟨7803164221960728644156531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202109481307152429437687 7803164221960728644156531)
                ·
                  refine ⟨11704746332941092966234797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7803164221960728644156531 11704746332941092966234797)
                  ·
                    refine ⟨4389279874852909862338049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11704746332941092966234797 4389279874852909862338049)
                    ·
                      refine ⟨3291959906139682396753537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389279874852909862338049 3291959906139682396753537)
                      ·
                        rfl

theorem cell23_6411069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6411069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411069 prefixEnd_6411069 := by exact prefixLift 6411069
  have htrace : WordTrace (prefixWord ++ tailWord_6411069) baseStart_6411069 baseEnd_6411069 := by
    simpa [prefixWord, tailWord_6411069, baseEnd_6411069] using wordTrace_append hprefix tailTrace_6411069
  have hstable : (prefixWord ++ tailWord_6411069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411069).length < 2 ^ (prefixWord ++ tailWord_6411069).sum := by decide
  have hdescent : baseEnd_6411069 < baseStart_6411069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411076 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6411076 : Nat := 118140960795 + 6411076 * 2 ^ 59
def prefixEnd_6411076 : Nat := 4983230072969 + 3 ^ 40 * 6411076 * 2
def baseEnd_6411076 : Nat := 3291963500504263869366005

theorem tailTrace_6411076 : CollatzResearch.WordTrace tailWord_6411076 prefixEnd_6411076 3291963500504263869366005 := by
  unfold tailWord_6411076
  simp only [CollatzResearch.WordTrace]
  refine ⟨116915575860887025727254541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155887434481182700969672721 116915575860887025727254541)
  ·
    refine ⟨43843340947832634647720453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116915575860887025727254541 43843340947832634647720453)
    ·
      refine ⟨8220626427718618996447585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43843340947832634647720453 8220626427718618996447585)
      ·
        refine ⟨6165469820788964247335689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8220626427718618996447585 6165469820788964247335689)
        ·
          refine ⟨4624102365591723185501767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6165469820788964247335689 4624102365591723185501767)
          ·
            refine ⟨6936153548387584778252651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624102365591723185501767 6936153548387584778252651)
            ·
              refine ⟨10404230322581377167378977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936153548387584778252651 10404230322581377167378977)
              ·
                refine ⟨7803172741936032875534233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10404230322581377167378977 7803172741936032875534233)
                ·
                  refine ⟨5852379556452024656650675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803172741936032875534233 5852379556452024656650675)
                  ·
                    refine ⟨8778569334678036984976013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5852379556452024656650675 8778569334678036984976013)
                    ·
                      refine ⟨3291963500504263869366005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778569334678036984976013 3291963500504263869366005)
                      ·
                        rfl

theorem cell23_6411076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6411076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411076 prefixEnd_6411076 := by exact prefixLift 6411076
  have htrace : WordTrace (prefixWord ++ tailWord_6411076) baseStart_6411076 baseEnd_6411076 := by
    simpa [prefixWord, tailWord_6411076, baseEnd_6411076] using wordTrace_append hprefix tailTrace_6411076
  have hstable : (prefixWord ++ tailWord_6411076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411076).length < 2 ^ (prefixWord ++ tailWord_6411076).sum := by decide
  have hdescent : baseEnd_6411076 < baseStart_6411076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411081 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_6411081 : Nat := 118140960795 + 6411081 * 2 ^ 59
def prefixEnd_6411081 : Nat := 4983230072969 + 3 ^ 40 * 6411081 * 2
def baseEnd_6411081 : Nat := 3291966067907536349803481

theorem tailTrace_6411081 : CollatzResearch.WordTrace tailWord_6411081 prefixEnd_6411081 3291966067907536349803481 := by
  unfold tailWord_6411081
  simp only [CollatzResearch.WordTrace]
  refine ⟨233831334086755937308441097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155887556057837291538960731 233831334086755937308441097)
  ·
    refine ⟨175373500565066952981330823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233831334086755937308441097 175373500565066952981330823)
    ·
      refine ⟨263060250847600429471996235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175373500565066952981330823 263060250847600429471996235)
      ·
        refine ⟨394590376271400644207994353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263060250847600429471996235 394590376271400644207994353)
        ·
          refine ⟨295942782203550483155995765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394590376271400644207994353 295942782203550483155995765)
          ·
            refine ⟨27744635831582857795874603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295942782203550483155995765 27744635831582857795874603)
            ·
              refine ⟨41616953747374286693811905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27744635831582857795874603 41616953747374286693811905)
              ·
                refine ⟨31212715310530715020358929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41616953747374286693811905 31212715310530715020358929)
                ·
                  refine ⟨23409536482898036265269197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31212715310530715020358929 23409536482898036265269197)
                  ·
                    refine ⟨8778576181086763599475949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23409536482898036265269197 8778576181086763599475949)
                    ·
                      refine ⟨3291966067907536349803481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778576181086763599475949 3291966067907536349803481)
                      ·
                        rfl

theorem cell23_6411081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_6411081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411081 prefixEnd_6411081 := by exact prefixLift 6411081
  have htrace : WordTrace (prefixWord ++ tailWord_6411081) baseStart_6411081 baseEnd_6411081 := by
    simpa [prefixWord, tailWord_6411081, baseEnd_6411081] using wordTrace_append hprefix tailTrace_6411081
  have hstable : (prefixWord ++ tailWord_6411081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411081).length < 2 ^ (prefixWord ++ tailWord_6411081).sum := by decide
  have hdescent : baseEnd_6411081 < baseStart_6411081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411091 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 7, 2]
def baseStart_6411091 : Nat := 118140960795 + 6411091 * 2 ^ 59
def prefixEnd_6411091 : Nat := 4983230072969 + 3 ^ 40 * 6411091 * 2
def baseEnd_6411091 : Nat := 3291971202714081310678435

theorem tailTrace_6411091 : CollatzResearch.WordTrace tailWord_6411091 prefixEnd_6411091 3291971202714081310678435 := by
  unfold tailWord_6411091
  simp only [CollatzResearch.WordTrace]
  refine ⟨233831698816719709016305127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155887799211146472677536751 233831698816719709016305127)
  ·
    refine ⟨350747548225079563524457691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233831698816719709016305127 350747548225079563524457691)
    ·
      refine ⟨526121322337619345286686537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350747548225079563524457691 526121322337619345286686537)
      ·
        refine ⟨394590991753214508965014903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526121322337619345286686537 394590991753214508965014903)
        ·
          refine ⟨591886487629821763447522355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394590991753214508965014903 591886487629821763447522355)
          ·
            refine ⟨887829731444732645171283533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591886487629821763447522355 887829731444732645171283533)
            ·
              refine ⟨332936149291774741939231325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887829731444732645171283533 332936149291774741939231325)
              ·
                refine ⟨124851055984415528227211747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332936149291774741939231325 124851055984415528227211747)
                ·
                  refine ⟨187276583976623292340817621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124851055984415528227211747 187276583976623292340817621)
                  ·
                    refine ⟨4389294936952108414237913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 187276583976623292340817621 4389294936952108414237913)
                    ·
                      refine ⟨3291971202714081310678435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389294936952108414237913 3291971202714081310678435)
                      ·
                        rfl

theorem cell23_6411091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7, 2].length) (baseStart_6411091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411091 prefixEnd_6411091 := by exact prefixLift 6411091
  have htrace : WordTrace (prefixWord ++ tailWord_6411091) baseStart_6411091 baseEnd_6411091 := by
    simpa [prefixWord, tailWord_6411091, baseEnd_6411091] using wordTrace_append hprefix tailTrace_6411091
  have hstable : (prefixWord ++ tailWord_6411091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411091).length < 2 ^ (prefixWord ++ tailWord_6411091).sum := by decide
  have hdescent : baseEnd_6411091 < baseStart_6411091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411121 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_6411121 : Nat := 118140960795 + 6411121 * 2 ^ 59
def prefixEnd_6411121 : Nat := 4983230072969 + 3 ^ 40 * 6411121 * 2
def baseEnd_6411121 : Nat := 3291986607133716193303297

theorem tailTrace_6411121 : CollatzResearch.WordTrace tailWord_6411121 prefixEnd_6411121 3291986607133716193303297 := by
  unfold tailWord_6411121
  simp only [CollatzResearch.WordTrace]
  refine ⟨233832793006611024139897217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155888528671074016093264811 233832793006611024139897217)
  ·
    refine ⟨175374594754958268104922913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233832793006611024139897217 175374594754958268104922913)
    ·
      refine ⟨131530946066218701078692185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175374594754958268104922913 131530946066218701078692185)
      ·
        refine ⟨98648209549664025809019139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131530946066218701078692185 98648209549664025809019139)
        ·
          refine ⟨147972314324496038713528709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98648209549664025809019139 147972314324496038713528709)
          ·
            refine ⟨27744808935843007258786633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147972314324496038713528709 27744808935843007258786633)
            ·
              refine ⟨20808606701882255444089975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27744808935843007258786633 20808606701882255444089975)
              ·
                refine ⟨31212910052823383166134963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20808606701882255444089975 31212910052823383166134963)
                ·
                  refine ⟨46819365079235074749202445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31212910052823383166134963 46819365079235074749202445)
                  ·
                    refine ⟨17557261904713153030950917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46819365079235074749202445 17557261904713153030950917)
                    ·
                      refine ⟨3291986607133716193303297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17557261904713153030950917 3291986607133716193303297)
                      ·
                        rfl

theorem cell23_6411121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_6411121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411121 prefixEnd_6411121 := by exact prefixLift 6411121
  have htrace : WordTrace (prefixWord ++ tailWord_6411121) baseStart_6411121 baseEnd_6411121 := by
    simpa [prefixWord, tailWord_6411121, baseEnd_6411121] using wordTrace_append hprefix tailTrace_6411121
  have hstable : (prefixWord ++ tailWord_6411121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411121).length < 2 ^ (prefixWord ++ tailWord_6411121).sum := by decide
  have hdescent : baseEnd_6411121 < baseStart_6411121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411131 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 5, 4]
def baseStart_6411131 : Nat := 118140960795 + 6411131 * 2 ^ 59
def prefixEnd_6411131 : Nat := 4983230072969 + 3 ^ 40 * 6411131 * 2
def baseEnd_6411131 : Nat := 1097330580646753718059417

theorem tailTrace_6411131 : CollatzResearch.WordTrace tailWord_6411131 prefixEnd_6411131 1097330580646753718059417 := by
  unfold tailWord_6411131
  simp only [CollatzResearch.WordTrace]
  refine ⟨233833157736574795847761247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155888771824383197231840831 233833157736574795847761247)
  ·
    refine ⟨350749736604862193771641871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233833157736574795847761247 350749736604862193771641871)
    ·
      refine ⟨526124604907293290657462807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350749736604862193771641871 526124604907293290657462807)
      ·
        refine ⟨789186907360939935986194211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526124604907293290657462807 789186907360939935986194211)
        ·
          refine ⟨1183780361041409903979291317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789186907360939935986194211 1183780361041409903979291317)
          ·
            refine ⟨110979408847632178498058561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1183780361041409903979291317 110979408847632178498058561)
            ·
              refine ⟨83234556635724133873543921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110979408847632178498058561 83234556635724133873543921)
              ·
                refine ⟨62425917476793100405157941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83234556635724133873543921 62425917476793100405157941)
                ·
                  refine ⟨5852429763449353162983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62425917476793100405157941 5852429763449353162983557)
                  ·
                    refine ⟨1097330580646753718059417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852429763449353162983557 1097330580646753718059417)
                    ·
                      rfl

theorem cell23_6411131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 4].length) (baseStart_6411131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411131 prefixEnd_6411131 := by exact prefixLift 6411131
  have htrace : WordTrace (prefixWord ++ tailWord_6411131) baseStart_6411131 baseEnd_6411131 := by
    simpa [prefixWord, tailWord_6411131, baseEnd_6411131] using wordTrace_append hprefix tailTrace_6411131
  have hstable : (prefixWord ++ tailWord_6411131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411131).length < 2 ^ (prefixWord ++ tailWord_6411131).sum := by decide
  have hdescent : baseEnd_6411131 < baseStart_6411131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411148 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_6411148 : Nat := 118140960795 + 6411148 * 2 ^ 59
def prefixEnd_6411148 : Nat := 4983230072969 + 3 ^ 40 * 6411148 * 2
def baseEnd_6411148 : Nat := 1097333490370462529221891

theorem tailTrace_6411148 : CollatzResearch.WordTrace tailWord_6411148 prefixEnd_6411148 1097333490370462529221891 := by
  unfold tailWord_6411148
  simp only [CollatzResearch.WordTrace]
  refine ⟨116916888888756603875565049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155889185185008805167420065 116916888888756603875565049)
  ·
    refine ⟨87687666666567452906673787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116916888888756603875565049 87687666666567452906673787)
    ·
      refine ⟨131531499999851179360010681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87687666666567452906673787 131531499999851179360010681)
      ·
        refine ⟨98648624999888384520008011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131531499999851179360010681 98648624999888384520008011)
        ·
          refine ⟨147972937499832576780012017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98648624999888384520008011 147972937499832576780012017)
          ·
            refine ⟨110979703124874432585009013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147972937499832576780012017 110979703124874432585009013)
            ·
              refine ⟨10404347167956978054844595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110979703124874432585009013 10404347167956978054844595)
              ·
                refine ⟨15606520751935467082266893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10404347167956978054844595 15606520751935467082266893)
                ·
                  refine ⟨5852445281975800155850085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15606520751935467082266893 5852445281975800155850085)
                  ·
                    refine ⟨1097333490370462529221891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852445281975800155850085 1097333490370462529221891)
                    ·
                      rfl

theorem cell23_6411148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_6411148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411148 prefixEnd_6411148 := by exact prefixLift 6411148
  have htrace : WordTrace (prefixWord ++ tailWord_6411148) baseStart_6411148 baseEnd_6411148 := by
    simpa [prefixWord, tailWord_6411148, baseEnd_6411148] using wordTrace_append hprefix tailTrace_6411148
  have hstable : (prefixWord ++ tailWord_6411148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411148).length < 2 ^ (prefixWord ++ tailWord_6411148).sum := by decide
  have hdescent : baseEnd_6411148 < baseStart_6411148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411171 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 3]
def baseStart_6411171 : Nat := 118140960795 + 6411171 * 2 ^ 59
def prefixEnd_6411171 : Nat := 4983230072969 + 3 ^ 40 * 6411171 * 2
def baseEnd_6411171 : Nat := 3292012281166440997678067

theorem tailTrace_6411171 : CollatzResearch.WordTrace tailWord_6411171 prefixEnd_6411171 3292012281166440997678067 := by
  unfold tailWord_6411171
  simp only [CollatzResearch.WordTrace]
  refine ⟨233834616656429882679217367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155889744437619921786144911 233834616656429882679217367)
  ·
    refine ⟨350751924984644824018826051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233834616656429882679217367 350751924984644824018826051)
    ·
      refine ⟨526127887476967236028239077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350751924984644824018826051 526127887476967236028239077)
      ·
        refine ⟨98648978901931356755294827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526127887476967236028239077 98648978901931356755294827)
        ·
          refine ⟨147973468352897035132942241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98648978901931356755294827 147973468352897035132942241)
          ·
            refine ⟨110980101264672776349706681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147973468352897035132942241 110980101264672776349706681)
            ·
              refine ⟨83235075948504582262280011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110980101264672776349706681 83235075948504582262280011)
              ·
                refine ⟨124852613922756873393420017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83235075948504582262280011 124852613922756873393420017)
                ·
                  refine ⟨93639460442067655045065013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124852613922756873393420017 93639460442067655045065013)
                  ·
                    refine ⟨8778699416443842660474845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93639460442067655045065013 8778699416443842660474845)
                    ·
                      refine ⟨3292012281166440997678067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778699416443842660474845 3292012281166440997678067)
                      ·
                        rfl

theorem cell23_6411171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_6411171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411171 prefixEnd_6411171 := by exact prefixLift 6411171
  have htrace : WordTrace (prefixWord ++ tailWord_6411171) baseStart_6411171 baseEnd_6411171 := by
    simpa [prefixWord, tailWord_6411171, baseEnd_6411171] using wordTrace_append hprefix tailTrace_6411171
  have hstable : (prefixWord ++ tailWord_6411171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411171).length < 2 ^ (prefixWord ++ tailWord_6411171).sum := by decide
  have hdescent : baseEnd_6411171 < baseStart_6411171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411222 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6411222 : Nat := 118140960795 + 6411222 * 2 ^ 59
def prefixEnd_6411222 : Nat := 4983230072969 + 3 ^ 40 * 6411222 * 2
def baseEnd_6411222 : Nat := 3292038468679820298140333

theorem tailTrace_6411222 : CollatzResearch.WordTrace tailWord_6411222 prefixEnd_6411222 3292038468679820298140333 := by
  unfold tailWord_6411222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614779798702819899332745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155890984519496745592882613 14614779798702819899332745)
  ·
    refine ⟨10961084849027114924499559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14614779798702819899332745 10961084849027114924499559)
    ·
      refine ⟨16441627273540672386749339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10961084849027114924499559 16441627273540672386749339)
      ·
        refine ⟨24662440910311008580124009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16441627273540672386749339 24662440910311008580124009)
        ·
          refine ⟨18496830682733256435093007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24662440910311008580124009 18496830682733256435093007)
          ·
            refine ⟨27745246024099884652639511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18496830682733256435093007 27745246024099884652639511)
            ·
              refine ⟨41617869036149826978959267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27745246024099884652639511 41617869036149826978959267)
              ·
                refine ⟨62426803554224740468438901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41617869036149826978959267 62426803554224740468438901)
                ·
                  refine ⟨5852512833208569418916147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62426803554224740468438901 5852512833208569418916147)
                  ·
                    refine ⟨8778769249812854128374221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5852512833208569418916147 8778769249812854128374221)
                    ·
                      refine ⟨3292038468679820298140333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778769249812854128374221 3292038468679820298140333)
                      ·
                        rfl

theorem cell23_6411222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6411222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411222 prefixEnd_6411222 := by exact prefixLift 6411222
  have htrace : WordTrace (prefixWord ++ tailWord_6411222) baseStart_6411222 baseEnd_6411222 := by
    simpa [prefixWord, tailWord_6411222, baseEnd_6411222] using wordTrace_append hprefix tailTrace_6411222
  have hstable : (prefixWord ++ tailWord_6411222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411222).length < 2 ^ (prefixWord ++ tailWord_6411222).sum := by decide
  have hdescent : baseEnd_6411222 < baseStart_6411222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411239 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6411239 : Nat := 118140960795 + 6411239 * 2 ^ 59
def prefixEnd_6411239 : Nat := 4983230072969 + 3 ^ 40 * 6411239 * 2
def baseEnd_6411239 : Nat := 3292047197850946731627755

theorem tailTrace_6411239 : CollatzResearch.WordTrace tailWord_6411239 prefixEnd_6411239 3292047197850946731627755 := by
  unfold tailWord_6411239
  simp only [CollatzResearch.WordTrace]
  refine ⟨233837096820183530292692771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155891397880122353528461847 233837096820183530292692771)
  ·
    refine ⟨350755645230275295439039157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233837096820183530292692771 350755645230275295439039157)
    ·
      refine ⟨32883341740338308947409921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 350755645230275295439039157 32883341740338308947409921)
      ·
        refine ⟨24662506305253731710557441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32883341740338308947409921 24662506305253731710557441)
        ·
          refine ⟨18496879728940298782918081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24662506305253731710557441 18496879728940298782918081)
          ·
            refine ⟨13872659796705224087188561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18496879728940298782918081 13872659796705224087188561)
            ·
              refine ⟨10404494847528918065391421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13872659796705224087188561 10404494847528918065391421)
              ·
                refine ⟨3901685567823344274521783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10404494847528918065391421 3901685567823344274521783)
                ·
                  refine ⟨5852528351735016411782675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901685567823344274521783 5852528351735016411782675)
                  ·
                    refine ⟨8778792527602524617674013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5852528351735016411782675 8778792527602524617674013)
                    ·
                      refine ⟨3292047197850946731627755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778792527602524617674013 3292047197850946731627755)
                      ·
                        rfl

theorem cell23_6411239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6411239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411239 prefixEnd_6411239 := by exact prefixLift 6411239
  have htrace : WordTrace (prefixWord ++ tailWord_6411239) baseStart_6411239 baseEnd_6411239 := by
    simpa [prefixWord, tailWord_6411239, baseEnd_6411239] using wordTrace_append hprefix tailTrace_6411239
  have hstable : (prefixWord ++ tailWord_6411239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411239).length < 2 ^ (prefixWord ++ tailWord_6411239).sum := by decide
  have hdescent : baseEnd_6411239 < baseStart_6411239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411242 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_6411242 : Nat := 118140960795 + 6411242 * 2 ^ 59
def prefixEnd_6411242 : Nat := 4983230072969 + 3 ^ 40 * 6411242 * 2
def baseEnd_6411242 : Nat := 1097349579430970073296747

theorem tailTrace_6411242 : CollatzResearch.WordTrace tailWord_6411242 prefixEnd_6411242 1097349579430970073296747 := by
  unfold tailWord_6411242
  simp only [CollatzResearch.WordTrace]
  refine ⟨58459301559793165451262995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155891470826115107870034653 58459301559793165451262995)
  ·
    refine ⟨87688952339689748176894493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58459301559793165451262995 87688952339689748176894493)
    ·
      refine ⟨32883357127383655566335435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87688952339689748176894493 32883357127383655566335435)
      ·
        refine ⟨49325035691075483349503153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32883357127383655566335435 49325035691075483349503153)
        ·
          refine ⟨36993776768306612512127365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49325035691075483349503153 36993776768306612512127365)
          ·
            refine ⟨6936333144057489846023881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36993776768306612512127365 6936333144057489846023881)
            ·
              refine ⟨5202249858043117384517911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6936333144057489846023881 5202249858043117384517911)
              ·
                refine ⟨7803374787064676076776867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202249858043117384517911 7803374787064676076776867)
                ·
                  refine ⟨11705062180597014115165301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7803374787064676076776867 11705062180597014115165301)
                  ·
                    refine ⟨1097349579430970073296747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11705062180597014115165301 1097349579430970073296747)
                    ·
                      rfl

theorem cell23_6411242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_6411242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411242 prefixEnd_6411242 := by exact prefixLift 6411242
  have htrace : WordTrace (prefixWord ++ tailWord_6411242) baseStart_6411242 baseEnd_6411242 := by
    simpa [prefixWord, tailWord_6411242, baseEnd_6411242] using wordTrace_append hprefix tailTrace_6411242
  have hstable : (prefixWord ++ tailWord_6411242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411242).length < 2 ^ (prefixWord ++ tailWord_6411242).sum := by decide
  have hdescent : baseEnd_6411242 < baseStart_6411242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411261 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_6411261 : Nat := 118140960795 + 6411261 * 2 ^ 59
def prefixEnd_6411261 : Nat := 4983230072969 + 3 ^ 40 * 6411261 * 2
def baseEnd_6411261 : Nat := 3292058494425345645552653

theorem tailTrace_6411261 : CollatzResearch.WordTrace tailWord_6411261 prefixEnd_6411261 3292058494425345645552653 := by
  unfold tailWord_6411261
  simp only [CollatzResearch.WordTrace]
  refine ⟨233837899226103828049993637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155891932817402552033329091 233837899226103828049993637)
  ·
    refine ⟨43844606104894467759373807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233837899226103828049993637 43844606104894467759373807)
    ·
      refine ⟨65766909157341701639060711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43844606104894467759373807 65766909157341701639060711)
      ·
        refine ⟨98650363736012552458591067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65766909157341701639060711 98650363736012552458591067)
        ·
          refine ⟨147975545604018828687886601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98650363736012552458591067 147975545604018828687886601)
          ·
            refine ⟨110981659203014121515914951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147975545604018828687886601 110981659203014121515914951)
            ·
              refine ⟨166472488804521182273872427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110981659203014121515914951 166472488804521182273872427)
              ·
                refine ⟨249708733206781773410808641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166472488804521182273872427 249708733206781773410808641)
                ·
                  refine ⟨187281549905086330058106481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249708733206781773410808641 187281549905086330058106481)
                  ·
                    refine ⟨140461162428814747543579861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187281549905086330058106481 140461162428814747543579861)
                    ·
                      refine ⟨3292058494425345645552653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140461162428814747543579861 3292058494425345645552653)
                      ·
                        rfl

theorem cell23_6411261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_6411261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411261 prefixEnd_6411261 := by exact prefixLift 6411261
  have htrace : WordTrace (prefixWord ++ tailWord_6411261) baseStart_6411261 baseEnd_6411261 := by
    simpa [prefixWord, tailWord_6411261, baseEnd_6411261] using wordTrace_append hprefix tailTrace_6411261
  have hstable : (prefixWord ++ tailWord_6411261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411261).length < 2 ^ (prefixWord ++ tailWord_6411261).sum := by decide
  have hdescent : baseEnd_6411261 < baseStart_6411261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411272 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 2, 4]
def baseStart_6411272 : Nat := 118140960795 + 6411272 * 2 ^ 59
def prefixEnd_6411272 : Nat := 4983230072969 + 3 ^ 40 * 6411272 * 2
def baseEnd_6411272 : Nat := 1097354714237515034171701

theorem tailTrace_6411272 : CollatzResearch.WordTrace tailWord_6411272 prefixEnd_6411272 1097354714237515034171701 := by
  unfold tailWord_6411272
  simp only [CollatzResearch.WordTrace]
  refine ⟨116919150214531988464322035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155892200286042651285762713 116919150214531988464322035)
  ·
    refine ⟨175378725321797982696483053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116919150214531988464322035 175378725321797982696483053)
    ·
      refine ⟨65767021995674243511181145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175378725321797982696483053 65767021995674243511181145)
      ·
        refine ⟨49325266496755682633385859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65767021995674243511181145 49325266496755682633385859)
        ·
          refine ⟨73987899745133523950078789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49325266496755682633385859 73987899745133523950078789)
          ·
            refine ⟨13872731202212535740639773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73987899745133523950078789 13872731202212535740639773)
            ·
              refine ⟨5202274200829700902739915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13872731202212535740639773 5202274200829700902739915)
              ·
                refine ⟨7803411301244551354109873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202274200829700902739915 7803411301244551354109873)
                ·
                  refine ⟨5852558475933413515582405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803411301244551354109873 5852558475933413515582405)
                  ·
                    refine ⟨1097354714237515034171701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852558475933413515582405 1097354714237515034171701)
                    ·
                      rfl

theorem cell23_6411272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_6411272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411272 prefixEnd_6411272 := by exact prefixLift 6411272
  have htrace : WordTrace (prefixWord ++ tailWord_6411272) baseStart_6411272 baseEnd_6411272 := by
    simpa [prefixWord, tailWord_6411272, baseEnd_6411272] using wordTrace_append hprefix tailTrace_6411272
  have hstable : (prefixWord ++ tailWord_6411272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411272).length < 2 ^ (prefixWord ++ tailWord_6411272).sum := by decide
  have hdescent : baseEnd_6411272 < baseStart_6411272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411275 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 4]
def baseStart_6411275 : Nat := 118140960795 + 6411275 * 2 ^ 59
def prefixEnd_6411275 : Nat := 4983230072969 + 3 ^ 40 * 6411275 * 2
def baseEnd_6411275 : Nat := 3292065683154508590777589

theorem tailTrace_6411275 : CollatzResearch.WordTrace tailWord_6411275 prefixEnd_6411275 3292065683154508590777589 := by
  unfold tailWord_6411275
  simp only [CollatzResearch.WordTrace]
  refine ⟨233838409848053108441003279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155892273232035405627335519 233838409848053108441003279)
  ·
    refine ⟨350757614772079662661504919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233838409848053108441003279 350757614772079662661504919)
    ·
      refine ⟨526136422158119493992257379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350757614772079662661504919 526136422158119493992257379)
      ·
        refine ⟨789204633237179240988386069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526136422158119493992257379 789204633237179240988386069)
        ·
          refine ⟨36993967182992776921330597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 789204633237179240988386069 36993967182992776921330597)
          ·
            refine ⟨6936368846811145672749487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36993967182992776921330597 6936368846811145672749487)
            ·
              refine ⟨10404553270216718509124231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936368846811145672749487 10404553270216718509124231)
              ·
                refine ⟨15606829905325077763686347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10404553270216718509124231 15606829905325077763686347)
                ·
                  refine ⟨23410244857987616645529521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15606829905325077763686347 23410244857987616645529521)
                  ·
                    refine ⟨17557683643490712484147141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23410244857987616645529521 17557683643490712484147141)
                    ·
                      refine ⟨3292065683154508590777589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17557683643490712484147141 3292065683154508590777589)
                      ·
                        rfl

theorem cell23_6411275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 4].length) (baseStart_6411275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411275 prefixEnd_6411275 := by exact prefixLift 6411275
  have htrace : WordTrace (prefixWord ++ tailWord_6411275) baseStart_6411275 baseEnd_6411275 := by
    simpa [prefixWord, tailWord_6411275, baseEnd_6411275] using wordTrace_append hprefix tailTrace_6411275
  have hstable : (prefixWord ++ tailWord_6411275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411275).length < 2 ^ (prefixWord ++ tailWord_6411275).sum := by decide
  have hdescent : baseEnd_6411275 < baseStart_6411275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411281 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_6411281 : Nat := 118140960795 + 6411281 * 2 ^ 59
def prefixEnd_6411281 : Nat := 4983230072969 + 3 ^ 40 * 6411281 * 2
def baseEnd_6411281 : Nat := 1097356254679478522434187

theorem tailTrace_6411281 : CollatzResearch.WordTrace tailWord_6411281 prefixEnd_6411281 1097356254679478522434187 := by
  unfold tailWord_6411281
  simp only [CollatzResearch.WordTrace]
  refine ⟨233838628686031371465721697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155892419124020914310481131 233838628686031371465721697)
  ·
    refine ⟨175378971514523528599291273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233838628686031371465721697 175378971514523528599291273)
    ·
      refine ⟨131534228635892646449468455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175378971514523528599291273 131534228635892646449468455)
      ·
        refine ⟨197301342953838969674202683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131534228635892646449468455 197301342953838969674202683)
        ·
          refine ⟨295952014430758454511304025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197301342953838969674202683 295952014430758454511304025)
          ·
            refine ⟨221964010823068840883478019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295952014430758454511304025 221964010823068840883478019)
            ·
              refine ⟨332946016234603261325217029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221964010823068840883478019 332946016234603261325217029)
              ·
                refine ⟨62427378043988111498478193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332946016234603261325217029 62427378043988111498478193)
                ·
                  refine ⟨46820533532991083623858645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62427378043988111498478193 46820533532991083623858645)
                  ·
                    refine ⟨1097356254679478522434187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46820533532991083623858645 1097356254679478522434187)
                    ·
                      rfl

theorem cell23_6411281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_6411281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411281 prefixEnd_6411281 := by exact prefixLift 6411281
  have htrace : WordTrace (prefixWord ++ tailWord_6411281) baseStart_6411281 baseEnd_6411281 := by
    simpa [prefixWord, tailWord_6411281, baseEnd_6411281] using wordTrace_append hprefix tailTrace_6411281
  have hstable : (prefixWord ++ tailWord_6411281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411281).length < 2 ^ (prefixWord ++ tailWord_6411281).sum := by decide
  have hdescent : baseEnd_6411281 < baseStart_6411281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411285 : List Nat := [1, 3, 2, 1, 4, 3, 2, 7]
def baseStart_6411285 : Nat := 118140960795 + 6411285 * 2 ^ 59
def prefixEnd_6411285 : Nat := 4983230072969 + 3 ^ 40 * 6411285 * 2
def baseEnd_6411285 : Nat := 121928548813372353764909

theorem tailTrace_6411285 : CollatzResearch.WordTrace tailWord_6411285 prefixEnd_6411285 121928548813372353764909 := by
  unfold tailWord_6411285
  simp only [CollatzResearch.WordTrace]
  refine ⟨233838774578016880148867309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155892516385344586765911539 233838774578016880148867309)
  ·
    refine ⟨87689540466756330055825241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233838774578016880148867309 87689540466756330055825241)
    ·
      refine ⟨65767155350067247541868931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87689540466756330055825241 65767155350067247541868931)
      ·
        refine ⟨98650733025100871312803397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65767155350067247541868931 98650733025100871312803397)
        ·
          refine ⟨18497012442206413371150637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98650733025100871312803397 18497012442206413371150637)
          ·
            refine ⟨6936379665827405014181489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18497012442206413371150637 6936379665827405014181489)
            ·
              refine ⟨5202284749370553760636117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6936379665827405014181489 5202284749370553760636117)
              ·
                refine ⟨121928548813372353764909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5202284749370553760636117 121928548813372353764909)
                ·
                  rfl

theorem cell23_6411285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 7].length) (baseStart_6411285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411285 prefixEnd_6411285 := by exact prefixLift 6411285
  have htrace : WordTrace (prefixWord ++ tailWord_6411285) baseStart_6411285 baseEnd_6411285 := by
    simpa [prefixWord, tailWord_6411285, baseEnd_6411285] using wordTrace_append hprefix tailTrace_6411285
  have hstable : (prefixWord ++ tailWord_6411285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411285).length < 2 ^ (prefixWord ++ tailWord_6411285).sum := by decide
  have hdescent : baseEnd_6411285 < baseStart_6411285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411295 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 3]
def baseStart_6411295 : Nat := 118140960795 + 6411295 * 2 ^ 59
def prefixEnd_6411295 : Nat := 4983230072969 + 3 ^ 40 * 6411295 * 2
def baseEnd_6411295 : Nat := 3292075952767598512527497

theorem tailTrace_6411295 : CollatzResearch.WordTrace tailWord_6411295 prefixEnd_6411295 3292075952767598512527497 := by
  unfold tailWord_6411295
  simp only [CollatzResearch.WordTrace]
  refine ⟨233839139307980651856731339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155892759538653767904487559 233839139307980651856731339)
  ·
    refine ⟨350758708961970977785097009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233839139307980651856731339 350758708961970977785097009)
    ·
      refine ⟨263069031721478233338822757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350758708961970977785097009 263069031721478233338822757)
      ·
        refine ⟨49325443447777168751029267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263069031721478233338822757 49325443447777168751029267)
        ·
          refine ⟨73988165171665753126543901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49325443447777168751029267 73988165171665753126543901)
          ·
            refine ⟨27745561939374657422453963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73988165171665753126543901 27745561939374657422453963)
            ·
              refine ⟨41618342909061986133680945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27745561939374657422453963 41618342909061986133680945)
              ·
                refine ⟨31213757181796489600260709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41618342909061986133680945 31213757181796489600260709)
                ·
                  refine ⟨5852579471586841800048883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31213757181796489600260709 5852579471586841800048883)
                  ·
                    refine ⟨8778869207380262700073325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5852579471586841800048883 8778869207380262700073325)
                    ·
                      refine ⟨3292075952767598512527497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778869207380262700073325 3292075952767598512527497)
                      ·
                        rfl

theorem cell23_6411295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_6411295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411295 prefixEnd_6411295 := by exact prefixLift 6411295
  have htrace : WordTrace (prefixWord ++ tailWord_6411295) baseStart_6411295 baseEnd_6411295 := by
    simpa [prefixWord, tailWord_6411295, baseEnd_6411295] using wordTrace_append hprefix tailTrace_6411295
  have hstable : (prefixWord ++ tailWord_6411295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411295).length < 2 ^ (prefixWord ++ tailWord_6411295).sum := by decide
  have hdescent : baseEnd_6411295 < baseStart_6411295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411329 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6411329 : Nat := 118140960795 + 6411329 * 2 ^ 59
def prefixEnd_6411329 : Nat := 4983230072969 + 3 ^ 40 * 6411329 * 2
def baseEnd_6411329 : Nat := 3292093411109851379502341

theorem tailTrace_6411329 : CollatzResearch.WordTrace tailWord_6411329 prefixEnd_6411329 3292093411109851379502341 := by
  unfold tailWord_6411329
  simp only [CollatzResearch.WordTrace]
  refine ⟨233840379389857475663469041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155893586259904983775646027 233840379389857475663469041)
  ·
    refine ⟨175380284542393106747601781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233840379389857475663469041 175380284542393106747601781)
    ·
      refine ⟨16441901675849353757587667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175380284542393106747601781 16441901675849353757587667)
      ·
        refine ⟨24662852513774030636381501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16441901675849353757587667 24662852513774030636381501)
        ·
          refine ⟨9248569692665261488643063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24662852513774030636381501 9248569692665261488643063)
          ·
            refine ⟨13872854538997892232964595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9248569692665261488643063 13872854538997892232964595)
            ·
              refine ⟨20809281808496838349446893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13872854538997892232964595 20809281808496838349446893)
              ·
                refine ⟨7803480678186314381042585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20809281808496838349446893 7803480678186314381042585)
                ·
                  refine ⟨5852610508639735785781939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803480678186314381042585 5852610508639735785781939)
                  ·
                    refine ⟨8778915762959603678672909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5852610508639735785781939 8778915762959603678672909)
                    ·
                      refine ⟨3292093411109851379502341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8778915762959603678672909 3292093411109851379502341)
                      ·
                        rfl

theorem cell23_6411329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6411329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411329 prefixEnd_6411329 := by exact prefixLift 6411329
  have htrace : WordTrace (prefixWord ++ tailWord_6411329) baseStart_6411329 baseEnd_6411329 := by
    simpa [prefixWord, tailWord_6411329, baseEnd_6411329] using wordTrace_append hprefix tailTrace_6411329
  have hstable : (prefixWord ++ tailWord_6411329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411329).length < 2 ^ (prefixWord ++ tailWord_6411329).sum := by decide
  have hdescent : baseEnd_6411329 < baseStart_6411329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411338 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_6411338 : Nat := 118140960795 + 6411338 * 2 ^ 59
def prefixEnd_6411338 : Nat := 4983230072969 + 3 ^ 40 * 6411338 * 2
def baseEnd_6411338 : Nat := 3292098032435741844289799

theorem tailTrace_6411338 : CollatzResearch.WordTrace tailWord_6411338 prefixEnd_6411338 3292098032435741844289799 := by
  unfold tailWord_6411338
  simp only [CollatzResearch.WordTrace]
  refine ⟨58460176911706217550136667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155893805097883246800364445 58460176911706217550136667)
  ·
    refine ⟨87690265367559326325205001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58460176911706217550136667 87690265367559326325205001)
    ·
      refine ⟨65767699025669494743903751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87690265367559326325205001 65767699025669494743903751)
      ·
        refine ⟨98651548538504242115855627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65767699025669494743903751 98651548538504242115855627)
        ·
          refine ⟨147977322807756363173783441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98651548538504242115855627 147977322807756363173783441)
          ·
            refine ⟨110982992105817272380337581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147977322807756363173783441 110982992105817272380337581)
            ·
              refine ⟨41618622039681477142626593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110982992105817272380337581 41618622039681477142626593)
              ·
                refine ⟨31213966529761107856969945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41618622039681477142626593 31213966529761107856969945)
                ·
                  refine ⟨23410474897320830892727459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31213966529761107856969945 23410474897320830892727459)
                  ·
                    refine ⟨35115712345981246339091189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23410474897320830892727459 35115712345981246339091189)
                    ·
                      refine ⟨3292098032435741844289799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35115712345981246339091189 3292098032435741844289799)
                      ·
                        rfl

theorem cell23_6411338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_6411338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411338 prefixEnd_6411338 := by exact prefixLift 6411338
  have htrace : WordTrace (prefixWord ++ tailWord_6411338) baseStart_6411338 baseEnd_6411338 := by
    simpa [prefixWord, tailWord_6411338, baseEnd_6411338] using wordTrace_append hprefix tailTrace_6411338
  have hstable : (prefixWord ++ tailWord_6411338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411338).length < 2 ^ (prefixWord ++ tailWord_6411338).sum := by decide
  have hdescent : baseEnd_6411338 < baseStart_6411338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411369 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 2, 2, 2]
def baseStart_6411369 : Nat := 118140960795 + 6411369 * 2 ^ 59
def prefixEnd_6411369 : Nat := 4983230072969 + 3 ^ 40 * 6411369 * 2
def baseEnd_6411369 : Nat := 3292113950336031223002157

theorem tailTrace_6411369 : CollatzResearch.WordTrace tailWord_6411369 prefixEnd_6411369 3292113950336031223002157 := by
  unfold tailWord_6411369
  simp only [CollatzResearch.WordTrace]
  refine ⟨233841838309712562494925161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155894558873141708329950107 233841838309712562494925161)
  ·
    refine ⟨175381378732284421871193871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233841838309712562494925161 175381378732284421871193871)
    ·
      refine ⟨263072068098426632806790807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175381378732284421871193871 263072068098426632806790807)
      ·
        refine ⟨394608102147639949210186211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263072068098426632806790807 394608102147639949210186211)
        ·
          refine ⟨591912153221459923815279317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394608102147639949210186211 591912153221459923815279317)
          ·
            refine ⟨13872941091127966964420609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 591912153221459923815279317 13872941091127966964420609)
            ·
              refine ⟨10404705818345975223315457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13872941091127966964420609 10404705818345975223315457)
              ·
                refine ⟨7803529363759481417486593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10404705818345975223315457 7803529363759481417486593)
                ·
                  refine ⟨5852647022819611063114945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803529363759481417486593 5852647022819611063114945)
                  ·
                    refine ⟨4389485267114708297336209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5852647022819611063114945 4389485267114708297336209)
                    ·
                      refine ⟨3292113950336031223002157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389485267114708297336209 3292113950336031223002157)
                      ·
                        rfl

theorem cell23_6411369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 2, 2].length) (baseStart_6411369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411369 prefixEnd_6411369 := by exact prefixLift 6411369
  have htrace : WordTrace (prefixWord ++ tailWord_6411369) baseStart_6411369 baseEnd_6411369 := by
    simpa [prefixWord, tailWord_6411369, baseEnd_6411369] using wordTrace_append hprefix tailTrace_6411369
  have hstable : (prefixWord ++ tailWord_6411369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411369).length < 2 ^ (prefixWord ++ tailWord_6411369).sum := by decide
  have hdescent : baseEnd_6411369 < baseStart_6411369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411375 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 5]
def baseStart_6411375 : Nat := 118140960795 + 6411375 * 2 ^ 59
def prefixEnd_6411375 : Nat := 4983230072969 + 3 ^ 40 * 6411375 * 2
def baseEnd_6411375 : Nat := 365790781246662022169681

theorem tailTrace_6411375 : CollatzResearch.WordTrace tailWord_6411375 prefixEnd_6411375 365790781246662022169681 := by
  unfold tailWord_6411375
  simp only [CollatzResearch.WordTrace]
  refine ⟨233842057147690825519643579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155894704765127217013095719 233842057147690825519643579)
  ·
    refine ⟨350763085721536238279465369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233842057147690825519643579 350763085721536238279465369)
    ·
      refine ⟨263072314291152178709599027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350763085721536238279465369 263072314291152178709599027)
      ·
        refine ⟨394608471436728268064398541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263072314291152178709599027 394608471436728268064398541)
        ·
          refine ⟨147978176788773100524149453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394608471436728268064398541 147978176788773100524149453)
          ·
            refine ⟨55491816295789912696556045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147978176788773100524149453 55491816295789912696556045)
            ·
              refine ⟨20809431110921217261208517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55491816295789912696556045 20809431110921217261208517)
              ·
                refine ⟨3901768333297728236476597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20809431110921217261208517 3901768333297728236476597)
                ·
                  refine ⟨365790781246662022169681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3901768333297728236476597 365790781246662022169681)
                  ·
                    rfl

theorem cell23_6411375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 5].length) (baseStart_6411375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411375 prefixEnd_6411375 := by exact prefixLift 6411375
  have htrace : WordTrace (prefixWord ++ tailWord_6411375) baseStart_6411375 baseEnd_6411375 := by
    simpa [prefixWord, tailWord_6411375, baseEnd_6411375] using wordTrace_append hprefix tailTrace_6411375
  have hstable : (prefixWord ++ tailWord_6411375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411375).length < 2 ^ (prefixWord ++ tailWord_6411375).sum := by decide
  have hdescent : baseEnd_6411375 < baseStart_6411375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411388 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_6411388 : Nat := 118140960795 + 6411388 * 2 ^ 59
def prefixEnd_6411388 : Nat := 4983230072969 + 3 ^ 40 * 6411388 * 2
def baseEnd_6411388 : Nat := 1097374568822822216221523

theorem tailTrace_6411388 : CollatzResearch.WordTrace tailWord_6411388 prefixEnd_6411388 1097374568822822216221523 := by
  unfold tailWord_6411388
  simp only [CollatzResearch.WordTrace]
  refine ⟨116921265648321864369933409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155895020864429152493244545 116921265648321864369933409)
  ·
    refine ⟨87690949236241398277450057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116921265648321864369933409 87690949236241398277450057)
    ·
      refine ⟨65768211927181048708087543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87690949236241398277450057 65768211927181048708087543)
      ·
        refine ⟨98652317890771573062131315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65768211927181048708087543 98652317890771573062131315)
        ·
          refine ⟨147978476836157359593196973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98652317890771573062131315 147978476836157359593196973)
          ·
            refine ⟨55491928813559009847448865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147978476836157359593196973 55491928813559009847448865)
            ·
              refine ⟨41618946610169257385586649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55491928813559009847448865 41618946610169257385586649)
              ·
                refine ⟨31214209957626943039189987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41618946610169257385586649 31214209957626943039189987)
                ·
                  refine ⟨46821314936440414558784981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31214209957626943039189987 46821314936440414558784981)
                  ·
                    refine ⟨1097374568822822216221523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46821314936440414558784981 1097374568822822216221523)
                    ·
                      rfl

theorem cell23_6411388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_6411388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411388 prefixEnd_6411388 := by exact prefixLift 6411388
  have htrace : WordTrace (prefixWord ++ tailWord_6411388) baseStart_6411388 baseEnd_6411388 := by
    simpa [prefixWord, tailWord_6411388, baseEnd_6411388] using wordTrace_append hprefix tailTrace_6411388
  have hstable : (prefixWord ++ tailWord_6411388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411388).length < 2 ^ (prefixWord ++ tailWord_6411388).sum := by decide
  have hdescent : baseEnd_6411388 < baseStart_6411388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411395 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 2, 5, 2]
def baseStart_6411395 : Nat := 118140960795 + 6411395 * 2 ^ 59
def prefixEnd_6411395 : Nat := 4983230072969 + 3 ^ 40 * 6411395 * 2
def baseEnd_6411395 : Nat := 3292127300833048121277037

theorem tailTrace_6411395 : CollatzResearch.WordTrace tailWord_6411395 prefixEnd_6411395 3292127300833048121277037 := by
  unfold tailWord_6411395
  simp only [CollatzResearch.WordTrace]
  refine ⟨233842786607618368935371639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155895191071745579290247759 233842786607618368935371639)
  ·
    refine ⟨350764179911427553403057459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233842786607618368935371639 350764179911427553403057459)
    ·
      refine ⟨526146269867141330104586189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350764179911427553403057459 526146269867141330104586189)
      ·
        refine ⟨197304851200177998789219821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526146269867141330104586189 197304851200177998789219821)
        ·
          refine ⟨73989319200066749545957433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197304851200177998789219821 73989319200066749545957433)
          ·
            refine ⟨55491989400050062159468075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73989319200066749545957433 55491989400050062159468075)
            ·
              refine ⟨83237984100075093239202113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55491989400050062159468075 83237984100075093239202113)
              ·
                refine ⟨62428488075056319929401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83237984100075093239202113 62428488075056319929401585)
                ·
                  refine ⟨46821366056292239947051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62428488075056319929401585 46821366056292239947051189)
                  ·
                    refine ⟨4389503067777397495036049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46821366056292239947051189 4389503067777397495036049)
                    ·
                      refine ⟨3292127300833048121277037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389503067777397495036049 3292127300833048121277037)
                      ·
                        rfl

theorem cell23_6411395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_6411395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411395 prefixEnd_6411395 := by exact prefixLift 6411395
  have htrace : WordTrace (prefixWord ++ tailWord_6411395) baseStart_6411395 baseEnd_6411395 := by
    simpa [prefixWord, tailWord_6411395, baseEnd_6411395] using wordTrace_append hprefix tailTrace_6411395
  have hstable : (prefixWord ++ tailWord_6411395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411395).length < 2 ^ (prefixWord ++ tailWord_6411395).sum := by decide
  have hdescent : baseEnd_6411395 < baseStart_6411395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411425 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6411425 : Nat := 118140960795 + 6411425 * 2 ^ 59
def prefixEnd_6411425 : Nat := 4983230072969 + 3 ^ 40 * 6411425 * 2
def baseEnd_6411425 : Nat := 3292142705252683003901899

theorem tailTrace_6411425 : CollatzResearch.WordTrace tailWord_6411425 prefixEnd_6411425 3292142705252683003901899 := by
  unfold tailWord_6411425
  simp only [CollatzResearch.WordTrace]
  refine ⟨233843880797509684058963729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155895920531673122705975819 233843880797509684058963729)
  ·
    refine ⟨175382910598132263044222797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233843880797509684058963729 175382910598132263044222797)
    ·
      refine ⟨65768591474299598641583549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175382910598132263044222797 65768591474299598641583549)
      ·
        refine ⟨24663221802862349490593831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65768591474299598641583549 24663221802862349490593831)
        ·
          refine ⟨36994832704293524235890747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24663221802862349490593831 36994832704293524235890747)
          ·
            refine ⟨55492249056440286353836121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36994832704293524235890747 55492249056440286353836121)
            ·
              refine ⟨41619186792330214765377091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55492249056440286353836121 41619186792330214765377091)
              ·
                refine ⟨62428780188495322148065637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41619186792330214765377091 62428780188495322148065637)
                ·
                  refine ⟨11705396285342872902762307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62428780188495322148065637 11705396285342872902762307)
                  ·
                    refine ⟨17558094428014309354143461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11705396285342872902762307 17558094428014309354143461)
                    ·
                      refine ⟨3292142705252683003901899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17558094428014309354143461 3292142705252683003901899)
                      ·
                        rfl

theorem cell23_6411425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6411425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411425 prefixEnd_6411425 := by exact prefixLift 6411425
  have htrace : WordTrace (prefixWord ++ tailWord_6411425) baseStart_6411425 baseEnd_6411425 := by
    simpa [prefixWord, tailWord_6411425, baseEnd_6411425] using wordTrace_append hprefix tailTrace_6411425
  have hstable : (prefixWord ++ tailWord_6411425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411425).length < 2 ^ (prefixWord ++ tailWord_6411425).sum := by decide
  have hdescent : baseEnd_6411425 < baseStart_6411425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411442 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_6411442 : Nat := 118140960795 + 6411442 * 2 ^ 59
def prefixEnd_6411442 : Nat := 4983230072969 + 3 ^ 40 * 6411442 * 2
def baseEnd_6411442 : Nat := 3292151434423809437389321

theorem tailTrace_6411442 : CollatzResearch.WordTrace tailWord_6411442 prefixEnd_6411442 3292151434423809437389321 := by
  unfold tailWord_6411442
  simp only [CollatzResearch.WordTrace]
  refine ⟨58461125209612023990583145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155896333892298730641555053 58461125209612023990583145)
  ·
    refine ⟨43845843907209017992937359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58461125209612023990583145 43845843907209017992937359)
    ·
      refine ⟨65768765860813526989406039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43845843907209017992937359 65768765860813526989406039)
      ·
        refine ⟨98653148791220290484109059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65768765860813526989406039 98653148791220290484109059)
        ·
          refine ⟨147979723186830435726163589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98653148791220290484109059 147979723186830435726163589)
          ·
            refine ⟨27746198097530706698655673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147979723186830435726163589 27746198097530706698655673)
            ·
              refine ⟨20809648573148030023991755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27746198097530706698655673 20809648573148030023991755)
              ·
                refine ⟨31214472859722045035987633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20809648573148030023991755 31214472859722045035987633)
                ·
                  refine ⟨23410854644791533776990725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31214472859722045035987633 23410854644791533776990725)
                  ·
                    refine ⟨4389535245898412583185761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23410854644791533776990725 4389535245898412583185761)
                    ·
                      refine ⟨3292151434423809437389321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389535245898412583185761 3292151434423809437389321)
                      ·
                        rfl

theorem cell23_6411442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_6411442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411442 prefixEnd_6411442 := by exact prefixLift 6411442
  have htrace : WordTrace (prefixWord ++ tailWord_6411442) baseStart_6411442 baseEnd_6411442 := by
    simpa [prefixWord, tailWord_6411442, baseEnd_6411442] using wordTrace_append hprefix tailTrace_6411442
  have hstable : (prefixWord ++ tailWord_6411442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411442).length < 2 ^ (prefixWord ++ tailWord_6411442).sum := by decide
  have hdescent : baseEnd_6411442 < baseStart_6411442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411452 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_6411452 : Nat := 118140960795 + 6411452 * 2 ^ 59
def prefixEnd_6411452 : Nat := 4983230072969 + 3 ^ 40 * 6411452 * 2
def baseEnd_6411452 : Nat := 1097385523076784799421425

theorem tailTrace_6411452 : CollatzResearch.WordTrace tailWord_6411452 prefixEnd_6411452 1097385523076784799421425 := by
  unfold tailWord_6411452
  simp only [CollatzResearch.WordTrace]
  refine ⟨116922432784205933835098305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155896577045607911780131073 116922432784205933835098305)
  ·
    refine ⟨87691824588154450376323729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116922432784205933835098305 87691824588154450376323729)
    ·
      refine ⟨65768868441115837782242797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87691824588154450376323729 65768868441115837782242797)
      ·
        refine ⟨24663325665418439168341049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65768868441115837782242797 24663325665418439168341049)
        ·
          refine ⟨18497494249063829376255787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24663325665418439168341049 18497494249063829376255787)
          ·
            refine ⟨27746241373595744064383681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18497494249063829376255787 27746241373595744064383681)
            ·
              refine ⟨20809681030196808048287761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27746241373595744064383681 20809681030196808048287761)
              ·
                refine ⟨15607260772647606036215821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20809681030196808048287761 15607260772647606036215821)
                ·
                  refine ⟨5852722789742852263580933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15607260772647606036215821 5852722789742852263580933)
                  ·
                    refine ⟨1097385523076784799421425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852722789742852263580933 1097385523076784799421425)
                    ·
                      rfl

theorem cell23_6411452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_6411452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411452 prefixEnd_6411452 := by exact prefixLift 6411452
  have htrace : WordTrace (prefixWord ++ tailWord_6411452) baseStart_6411452 baseEnd_6411452 := by
    simpa [prefixWord, tailWord_6411452, baseEnd_6411452] using wordTrace_append hprefix tailTrace_6411452
  have hstable : (prefixWord ++ tailWord_6411452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411452).length < 2 ^ (prefixWord ++ tailWord_6411452).sum := by decide
  have hdescent : baseEnd_6411452 < baseStart_6411452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411502 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_6411502 : Nat := 118140960795 + 6411502 * 2 ^ 59
def prefixEnd_6411502 : Nat := 4983230072969 + 3 ^ 40 * 6411502 * 2
def baseEnd_6411502 : Nat := 3292182243263079202639045

theorem tailTrace_6411502 : CollatzResearch.WordTrace tailWord_6411502 prefixEnd_6411502 3292182243263079202639045 := by
  unfold tailWord_6411502
  simp only [CollatzResearch.WordTrace]
  refine ⟨29230836152278840776189595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155897792812153817473011173 29230836152278840776189595)
  ·
    refine ⟨43846254228418261164284393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29230836152278840776189595 43846254228418261164284393)
    ·
      refine ⟨32884690671313695873213295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43846254228418261164284393 32884690671313695873213295)
      ·
        refine ⟨49327036006970543809819943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32884690671313695873213295 49327036006970543809819943)
        ·
          refine ⟨73990554010455815714729915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49327036006970543809819943 73990554010455815714729915)
          ·
            refine ⟨110985831015683723572094873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73990554010455815714729915 110985831015683723572094873)
            ·
              refine ⟨83239373261762792679071155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110985831015683723572094873 83239373261762792679071155)
              ·
                refine ⟨124859059892644189018606733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83239373261762792679071155 124859059892644189018606733)
                ·
                  refine ⟨46822147459741570881977525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124859059892644189018606733 46822147459741570881977525)
                  ·
                    refine ⟨4389576324350772270185393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46822147459741570881977525 4389576324350772270185393)
                    ·
                      refine ⟨3292182243263079202639045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389576324350772270185393 3292182243263079202639045)
                      ·
                        rfl

theorem cell23_6411502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_6411502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411502 prefixEnd_6411502 := by exact prefixLift 6411502
  have htrace : WordTrace (prefixWord ++ tailWord_6411502) baseStart_6411502 baseEnd_6411502 := by
    simpa [prefixWord, tailWord_6411502, baseEnd_6411502] using wordTrace_append hprefix tailTrace_6411502
  have hstable : (prefixWord ++ tailWord_6411502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411502).length < 2 ^ (prefixWord ++ tailWord_6411502).sum := by decide
  have hdescent : baseEnd_6411502 < baseStart_6411502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411519 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 2, 3, 2]
def baseStart_6411519 : Nat := 118140960795 + 6411519 * 2 ^ 59
def prefixEnd_6411519 : Nat := 4983230072969 + 3 ^ 40 * 6411519 * 2
def baseEnd_6411519 : Nat := 3292190972434205636126467

theorem tailTrace_6411519 : CollatzResearch.WordTrace tailWord_6411519 prefixEnd_6411519 3292190972434205636126467 := by
  unfold tailWord_6411519
  simp only [CollatzResearch.WordTrace]
  refine ⟨233847309259169138112885611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155898206172779425408590407 233847309259169138112885611)
  ·
    refine ⟨350770963888753707169328417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233847309259169138112885611 350770963888753707169328417)
    ·
      refine ⟨263078222916565280376996313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350770963888753707169328417 263078222916565280376996313)
      ·
        refine ⟨197308667187423960282747235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263078222916565280376996313 197308667187423960282747235)
        ·
          refine ⟨295963000781135940424120853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197308667187423960282747235 295963000781135940424120853)
          ·
            refine ⟨13873265661615747207380665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 295963000781135940424120853 13873265661615747207380665)
            ·
              refine ⟨10404949246211810405535499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13873265661615747207380665 10404949246211810405535499)
              ·
                refine ⟨15607423869317715608303249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10404949246211810405535499 15607423869317715608303249)
                ·
                  refine ⟨11705567901988286706227437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15607423869317715608303249 11705567901988286706227437)
                  ·
                    refine ⟨4389587963245607514835289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11705567901988286706227437 4389587963245607514835289)
                    ·
                      refine ⟨3292190972434205636126467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389587963245607514835289 3292190972434205636126467)
                      ·
                        rfl

theorem cell23_6411519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_6411519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411519 prefixEnd_6411519 := by exact prefixLift 6411519
  have htrace : WordTrace (prefixWord ++ tailWord_6411519) baseStart_6411519 baseEnd_6411519 := by
    simpa [prefixWord, tailWord_6411519, baseEnd_6411519] using wordTrace_append hprefix tailTrace_6411519
  have hstable : (prefixWord ++ tailWord_6411519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411519).length < 2 ^ (prefixWord ++ tailWord_6411519).sum := by decide
  have hdescent : baseEnd_6411519 < baseStart_6411519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411525 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_6411525 : Nat := 118140960795 + 6411525 * 2 ^ 59
def prefixEnd_6411525 : Nat := 4983230072969 + 3 ^ 40 * 6411525 * 2
def baseEnd_6411525 : Nat := 1097398017772710870883813

theorem tailTrace_6411525 : CollatzResearch.WordTrace tailWord_6411525 prefixEnd_6411525 1097398017772710870883813 := by
  unfold tailWord_6411525
  simp only [CollatzResearch.WordTrace]
  refine ⟨233847528097147401137604029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155898352064764934091736019 233847528097147401137604029)
  ·
    refine ⟨87692823036430275426601511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233847528097147401137604029 87692823036430275426601511)
    ·
      refine ⟨131539234554645413139902267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87692823036430275426601511 131539234554645413139902267)
      ·
        refine ⟨197308851831968119709853401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131539234554645413139902267 197308851831968119709853401)
        ·
          refine ⟨147981638873976089782390051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197308851831968119709853401 147981638873976089782390051)
          ·
            refine ⟨221972458310964134673585077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147981638873976089782390051 221972458310964134673585077)
            ·
              refine ⟨20809917966652887625648601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221972458310964134673585077 20809917966652887625648601)
              ·
                refine ⟨15607438474989665719236451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20809917966652887625648601 15607438474989665719236451)
                ·
                  refine ⟨23411157712484498578854677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15607438474989665719236451 23411157712484498578854677)
                  ·
                    refine ⟨1097398017772710870883813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23411157712484498578854677 1097398017772710870883813)
                    ·
                      rfl

theorem cell23_6411525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_6411525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411525 prefixEnd_6411525 := by exact prefixLift 6411525
  have htrace : WordTrace (prefixWord ++ tailWord_6411525) baseStart_6411525 baseEnd_6411525 := by
    simpa [prefixWord, tailWord_6411525, baseEnd_6411525] using wordTrace_append hprefix tailTrace_6411525
  have hstable : (prefixWord ++ tailWord_6411525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411525).length < 2 ^ (prefixWord ++ tailWord_6411525).sum := by decide
  have hdescent : baseEnd_6411525 < baseStart_6411525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411555 : List Nat := [1, 1, 1, 4, 2, 3, 3, 8]
def baseStart_6411555 : Nat := 118140960795 + 6411555 * 2 ^ 59
def prefixEnd_6411555 : Nat := 4983230072969 + 3 ^ 40 * 6411555 * 2
def baseEnd_6411555 : Nat := 121933683619917314639863

theorem tailTrace_6411555 : CollatzResearch.WordTrace tailWord_6411555 prefixEnd_6411555 121933683619917314639863 := by
  unfold tailWord_6411555
  simp only [CollatzResearch.WordTrace]
  refine ⟨233848622287038716261196119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155899081524692477507464079 233848622287038716261196119)
  ·
    refine ⟨350772933430558074391794179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233848622287038716261196119 350772933430558074391794179)
    ·
      refine ⟨526159400145837111587691269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350772933430558074391794179 526159400145837111587691269)
      ·
        refine ⟨98654887527344458422692113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526159400145837111587691269 98654887527344458422692113)
        ·
          refine ⟨73991165645508343817019085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98654887527344458422692113 73991165645508343817019085)
          ·
            refine ⟨27746687117065628931382157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73991165645508343817019085 27746687117065628931382157)
            ·
              refine ⟨10405007668899610849268309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27746687117065628931382157 10405007668899610849268309)
              ·
                refine ⟨121933683619917314639863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10405007668899610849268309 121933683619917314639863)
                ·
                  rfl

theorem cell23_6411555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 8].length) (baseStart_6411555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411555 prefixEnd_6411555 := by exact prefixLift 6411555
  have htrace : WordTrace (prefixWord ++ tailWord_6411555) baseStart_6411555 baseEnd_6411555 := by
    simpa [prefixWord, tailWord_6411555, baseEnd_6411555] using wordTrace_append hprefix tailTrace_6411555
  have hstable : (prefixWord ++ tailWord_6411555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411555).length < 2 ^ (prefixWord ++ tailWord_6411555).sum := by decide
  have hdescent : baseEnd_6411555 < baseStart_6411555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411583 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 1, 2, 2]
def baseStart_6411583 : Nat := 118140960795 + 6411583 * 2 ^ 59
def prefixEnd_6411583 : Nat := 4983230072969 + 3 ^ 40 * 6411583 * 2
def baseEnd_6411583 : Nat := 3292223835196093385726173

theorem tailTrace_6411583 : CollatzResearch.WordTrace tailWord_6411583 prefixEnd_6411583 3292223835196093385726173 := by
  unfold tailWord_6411583
  simp only [CollatzResearch.WordTrace]
  refine ⟨233849643530937277043215403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155899762353958184695476935 233849643530937277043215403)
  ·
    refine ⟨350774465296405915564823105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233849643530937277043215403 350774465296405915564823105)
    ·
      refine ⟨263080848972304436673617329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350774465296405915564823105 263080848972304436673617329)
      ·
        refine ⟨197310636729228327505212997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263080848972304436673617329 197310636729228327505212997)
        ·
          refine ⟨36995744386730311407227437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197310636729228327505212997 36995744386730311407227437)
          ·
            refine ⟨13873404145023866777710289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36995744386730311407227437 13873404145023866777710289)
            ·
              refine ⟨10405053108767900083282717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13873404145023866777710289 10405053108767900083282717)
              ·
                refine ⟨3901894915787962531231019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10405053108767900083282717 3901894915787962531231019)
                ·
                  refine ⟨5852842373681943796846529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901894915787962531231019 5852842373681943796846529)
                  ·
                    refine ⟨4389631780261457847634897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5852842373681943796846529 4389631780261457847634897)
                    ·
                      refine ⟨3292223835196093385726173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389631780261457847634897 3292223835196093385726173)
                      ·
                        rfl

theorem cell23_6411583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_6411583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411583 prefixEnd_6411583 := by exact prefixLift 6411583
  have htrace : WordTrace (prefixWord ++ tailWord_6411583) baseStart_6411583 baseEnd_6411583 := by
    simpa [prefixWord, tailWord_6411583, baseEnd_6411583] using wordTrace_append hprefix tailTrace_6411583
  have hstable : (prefixWord ++ tailWord_6411583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411583).length < 2 ^ (prefixWord ++ tailWord_6411583).sum := by decide
  have hdescent : baseEnd_6411583 < baseStart_6411583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411639 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 6, 2, 2]
def baseStart_6411639 : Nat := 118140960795 + 6411639 * 2 ^ 59
def prefixEnd_6411639 : Nat := 4983230072969 + 3 ^ 40 * 6411639 * 2
def baseEnd_6411639 : Nat := 3292252590112745166625915

theorem tailTrace_6411639 : CollatzResearch.WordTrace tailWord_6411639 prefixEnd_6411639 3292252590112745166625915 := by
  unfold tailWord_6411639
  simp only [CollatzResearch.WordTrace]
  refine ⟨233851686018734398607253971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155901124012489599071502647 233851686018734398607253971)
  ·
    refine ⟨350777529028101597910880957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233851686018734398607253971 350777529028101597910880957)
    ·
      refine ⟨131541573385538099216580359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350777529028101597910880957 131541573385538099216580359)
      ·
        refine ⟨197312360078307148824870539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131541573385538099216580359 197312360078307148824870539)
        ·
          refine ⟨295968540117460723237305809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197312360078307148824870539 295968540117460723237305809)
          ·
            refine ⟨221976405088095542427979357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295968540117460723237305809 221976405088095542427979357)
            ·
              refine ⟨83241151908035828410492259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221976405088095542427979357 83241151908035828410492259)
              ·
                refine ⟨124861727862053742615738389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83241151908035828410492259 124861727862053742615738389)
                ·
                  refine ⟨5852893493533769185112737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124861727862053742615738389 5852893493533769185112737)
                  ·
                    refine ⟨4389670120150326888834553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5852893493533769185112737 4389670120150326888834553)
                    ·
                      refine ⟨3292252590112745166625915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389670120150326888834553 3292252590112745166625915)
                      ·
                        rfl

theorem cell23_6411639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_6411639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411639 prefixEnd_6411639 := by exact prefixLift 6411639
  have htrace : WordTrace (prefixWord ++ tailWord_6411639) baseStart_6411639 baseEnd_6411639 := by
    simpa [prefixWord, tailWord_6411639, baseEnd_6411639] using wordTrace_append hprefix tailTrace_6411639
  have hstable : (prefixWord ++ tailWord_6411639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411639).length < 2 ^ (prefixWord ++ tailWord_6411639).sum := by decide
  have hdescent : baseEnd_6411639 < baseStart_6411639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411656 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_6411656 : Nat := 118140960795 + 6411656 * 2 ^ 59
def prefixEnd_6411656 : Nat := 4983230072969 + 3 ^ 40 * 6411656 * 2
def baseEnd_6411656 : Nat := 3292261319283871600113337

theorem tailTrace_6411656 : CollatzResearch.WordTrace tailWord_6411656 prefixEnd_6411656 3292261319283871600113337 := by
  unfold tailWord_6411656
  simp only [CollatzResearch.WordTrace]
  refine ⟨116926153029836405255311411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155901537373115207007081881 116926153029836405255311411)
  ·
    refine ⟨175389229544754607882967117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116926153029836405255311411 175389229544754607882967117)
    ·
      refine ⟨65770961079282977956112669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175389229544754607882967117 65770961079282977956112669)
      ·
        refine ⟨24664110404731116733542251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65770961079282977956112669 24664110404731116733542251)
        ·
          refine ⟨36996165607096675100313377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24664110404731116733542251 36996165607096675100313377)
          ·
            refine ⟨27747124205322506325235033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36996165607096675100313377 27747124205322506325235033)
            ·
              refine ⟨20810343153991879743926275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27747124205322506325235033 20810343153991879743926275)
              ·
                refine ⟨31215514730987819615889413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20810343153991879743926275 31215514730987819615889413)
                ·
                  refine ⟨5852909012060216177979265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31215514730987819615889413 5852909012060216177979265)
                  ·
                    refine ⟨4389681759045162133484449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5852909012060216177979265 4389681759045162133484449)
                    ·
                      refine ⟨3292261319283871600113337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389681759045162133484449 3292261319283871600113337)
                      ·
                        rfl

theorem cell23_6411656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_6411656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411656 prefixEnd_6411656 := by exact prefixLift 6411656
  have htrace : WordTrace (prefixWord ++ tailWord_6411656) baseStart_6411656 baseEnd_6411656 := by
    simpa [prefixWord, tailWord_6411656, baseEnd_6411656] using wordTrace_append hprefix tailTrace_6411656
  have hstable : (prefixWord ++ tailWord_6411656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411656).length < 2 ^ (prefixWord ++ tailWord_6411656).sum := by decide
  have hdescent : baseEnd_6411656 < baseStart_6411656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411673 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 2, 2, 2]
def baseStart_6411673 : Nat := 118140960795 + 6411673 * 2 ^ 59
def prefixEnd_6411673 : Nat := 4983230072969 + 3 ^ 40 * 6411673 * 2
def baseEnd_6411673 : Nat := 3292270048454998033600759

theorem tailTrace_6411673 : CollatzResearch.WordTrace tailWord_6411673 prefixEnd_6411673 3292270048454998033600759 := by
  unfold tailWord_6411673
  simp only [CollatzResearch.WordTrace]
  refine ⟨233852926100611222413991673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155901950733740814942661115 233852926100611222413991673)
  ·
    refine ⟨175389694575458416810493755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233852926100611222413991673 175389694575458416810493755)
    ·
      refine ⟨263084541863187625215740633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175389694575458416810493755 263084541863187625215740633)
      ·
        refine ⟨197313406397390718911805475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263084541863187625215740633 197313406397390718911805475)
        ·
          refine ⟨295970109596086078367708213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197313406397390718911805475 295970109596086078367708213)
          ·
            refine ⟨27747197774633069846972645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295970109596086078367708213 27747197774633069846972645)
            ·
              refine ⟨5202599582743700596307371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27747197774633069846972645 5202599582743700596307371)
              ·
                refine ⟨7803899374115550894461057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202599582743700596307371 7803899374115550894461057)
                ·
                  refine ⟨5852924530586663170845793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803899374115550894461057 5852924530586663170845793)
                  ·
                    refine ⟨4389693397939997378134345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5852924530586663170845793 4389693397939997378134345)
                    ·
                      refine ⟨3292270048454998033600759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389693397939997378134345 3292270048454998033600759)
                      ·
                        rfl

theorem cell23_6411673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_6411673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411673 prefixEnd_6411673 := by exact prefixLift 6411673
  have htrace : WordTrace (prefixWord ++ tailWord_6411673) baseStart_6411673 baseEnd_6411673 := by
    simpa [prefixWord, tailWord_6411673, baseEnd_6411673] using wordTrace_append hprefix tailTrace_6411673
  have hstable : (prefixWord ++ tailWord_6411673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411673).length < 2 ^ (prefixWord ++ tailWord_6411673).sum := by decide
  have hdescent : baseEnd_6411673 < baseStart_6411673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411692 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_6411692 : Nat := 118140960795 + 6411692 * 2 ^ 59
def prefixEnd_6411692 : Nat := 4983230072969 + 3 ^ 40 * 6411692 * 2
def baseEnd_6411692 : Nat := 1097426601529144486421057

theorem tailTrace_6411692 : CollatzResearch.WordTrace tailWord_6411692 prefixEnd_6411692 1097426601529144486421057 := by
  unfold tailWord_6411692
  simp only [CollatzResearch.WordTrace]
  refine ⟨116926809543771194329466665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155902412725028259105955553 116926809543771194329466665)
  ·
    refine ⟨87695107157828395747099999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116926809543771194329466665 87695107157828395747099999)
    ·
      refine ⟨131542660736742593620649999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87695107157828395747099999 131542660736742593620649999)
      ·
        refine ⟨197313991105113890430974999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131542660736742593620649999 197313991105113890430974999)
        ·
          refine ⟨295970986657670835646462499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197313991105113890430974999 295970986657670835646462499)
          ·
            refine ⟨443956479986506253469693749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295970986657670835646462499 443956479986506253469693749)
            ·
              refine ⟨41620919998734961262783789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 443956479986506253469693749 41620919998734961262783789)
              ·
                refine ⟨15607844999525610473543921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41620919998734961262783789 15607844999525610473543921)
                ·
                  refine ⟨11705883749644207855157941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15607844999525610473543921 11705883749644207855157941)
                  ·
                    refine ⟨1097426601529144486421057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11705883749644207855157941 1097426601529144486421057)
                    ·
                      rfl

theorem cell23_6411692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_6411692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411692 prefixEnd_6411692 := by exact prefixLift 6411692
  have htrace : WordTrace (prefixWord ++ tailWord_6411692) baseStart_6411692 baseEnd_6411692 := by
    simpa [prefixWord, tailWord_6411692, baseEnd_6411692] using wordTrace_append hprefix tailTrace_6411692
  have hstable : (prefixWord ++ tailWord_6411692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411692).length < 2 ^ (prefixWord ++ tailWord_6411692).sum := by decide
  have hdescent : baseEnd_6411692 < baseStart_6411692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411716 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_6411716 : Nat := 118140960795 + 6411716 * 2 ^ 59
def prefixEnd_6411716 : Nat := 4983230072969 + 3 ^ 40 * 6411716 * 2
def baseEnd_6411716 : Nat := 3292292128123141365363061

theorem tailTrace_6411716 : CollatzResearch.WordTrace tailWord_6411716 prefixEnd_6411716 3292292128123141365363061 := by
  unfold tailWord_6411716
  simp only [CollatzResearch.WordTrace]
  refine ⟨116927247219727720378903501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155902996292970293838538001 116927247219727720378903501)
  ·
    refine ⟨43847717707397895142088813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116927247219727720378903501 43847717707397895142088813)
    ·
      refine ⟨16442894140274210678283305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43847717707397895142088813 16442894140274210678283305)
      ·
        refine ⟨12332170605205658008712479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16442894140274210678283305 12332170605205658008712479)
        ·
          refine ⟨18498255907808487013068719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12332170605205658008712479 18498255907808487013068719)
          ·
            refine ⟨27747383861712730519603079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18498255907808487013068719 27747383861712730519603079)
            ·
              refine ⟨41621075792569095779404619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27747383861712730519603079 41621075792569095779404619)
              ·
                refine ⟨62431613688853643669106929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41621075792569095779404619 62431613688853643669106929)
                ·
                  refine ⟨46823710266640232751830197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62431613688853643669106929 46823710266640232751830197)
                  ·
                    refine ⟨4389722837497521820484081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46823710266640232751830197 4389722837497521820484081)
                    ·
                      refine ⟨3292292128123141365363061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4389722837497521820484081 3292292128123141365363061)
                      ·
                        rfl

theorem cell23_6411716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_6411716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411716 prefixEnd_6411716 := by exact prefixLift 6411716
  have htrace : WordTrace (prefixWord ++ tailWord_6411716) baseStart_6411716 baseEnd_6411716 := by
    simpa [prefixWord, tailWord_6411716, baseEnd_6411716] using wordTrace_append hprefix tailTrace_6411716
  have hstable : (prefixWord ++ tailWord_6411716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411716).length < 2 ^ (prefixWord ++ tailWord_6411716).sum := by decide
  have hdescent : baseEnd_6411716 < baseStart_6411716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411752 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 8]
def baseStart_6411752 : Nat := 118140960795 + 6411752 * 2 ^ 59
def prefixEnd_6411752 : Nat := 4983230072969 + 3 ^ 40 * 6411752 * 2
def baseEnd_6411752 : Nat := 365812290380744802723655

theorem tailTrace_6411752 : CollatzResearch.WordTrace tailWord_6411752 prefixEnd_6411752 365812290380744802723655 := by
  unfold tailWord_6411752
  simp only [CollatzResearch.WordTrace]
  refine ⟨116927903733662509453058755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155903871644883345937411673 116927903733662509453058755)
  ·
    refine ⟨175391855600493764179588133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116927903733662509453058755 175391855600493764179588133)
    ·
      refine ⟨32885972925092580783672775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175391855600493764179588133 32885972925092580783672775)
      ·
        refine ⟨49328959387638871175509163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32885972925092580783672775 49328959387638871175509163)
        ·
          refine ⟨73993439081458306763263745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49328959387638871175509163 73993439081458306763263745)
          ·
            refine ⟨55495079311093730072447809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73993439081458306763263745 55495079311093730072447809)
            ·
              refine ⟨41621309483320297554335857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55495079311093730072447809 41621309483320297554335857)
              ·
                refine ⟨31215982112490223165751893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41621309483320297554335857 31215982112490223165751893)
                ·
                  refine ⟨365812290380744802723655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31215982112490223165751893 365812290380744802723655)
                  ·
                    rfl

theorem cell23_6411752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_6411752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411752 prefixEnd_6411752 := by exact prefixLift 6411752
  have htrace : WordTrace (prefixWord ++ tailWord_6411752) baseStart_6411752 baseEnd_6411752 := by
    simpa [prefixWord, tailWord_6411752, baseEnd_6411752] using wordTrace_append hprefix tailTrace_6411752
  have hstable : (prefixWord ++ tailWord_6411752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411752).length < 2 ^ (prefixWord ++ tailWord_6411752).sum := by decide
  have hdescent : baseEnd_6411752 < baseStart_6411752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411772 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_6411772 : Nat := 118140960795 + 6411772 * 2 ^ 59
def prefixEnd_6411772 : Nat := 4983230072969 + 3 ^ 40 * 6411772 * 2
def baseEnd_6411772 : Nat := 3292320883039793146262803

theorem tailTrace_6411772 : CollatzResearch.WordTrace tailWord_6411772 prefixEnd_6411772 3292320883039793146262803 := by
  unfold tailWord_6411772
  simp only [CollatzResearch.WordTrace]
  refine ⟨116928268463626281160922785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155904357951501708214563713 116928268463626281160922785)
  ·
    refine ⟨87696201347719710870692089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116928268463626281160922785 87696201347719710870692089)
    ·
      refine ⟨65772151010789783153019067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87696201347719710870692089 65772151010789783153019067)
      ·
        refine ⟨98658226516184674729528601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65772151010789783153019067 98658226516184674729528601)
        ·
          refine ⟨73993669887138506047146451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98658226516184674729528601 73993669887138506047146451)
          ·
            refine ⟨110990504830707759070719677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73993669887138506047146451 110990504830707759070719677)
            ·
              refine ⟨41621439311515409651519879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110990504830707759070719677 41621439311515409651519879)
              ·
                refine ⟨62432158967273114477279819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41621439311515409651519879 62432158967273114477279819)
                ·
                  refine ⟨93648238450909671715919729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62432158967273114477279819 93648238450909671715919729)
                  ·
                    refine ⟨70236178838182253786939797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93648238450909671715919729 70236178838182253786939797)
                    ·
                      refine ⟨3292320883039793146262803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70236178838182253786939797 3292320883039793146262803)
                      ·
                        rfl

theorem cell23_6411772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_6411772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411772 prefixEnd_6411772 := by exact prefixLift 6411772
  have htrace : WordTrace (prefixWord ++ tailWord_6411772) baseStart_6411772 baseEnd_6411772 := by
    simpa [prefixWord, tailWord_6411772, baseEnd_6411772] using wordTrace_append hprefix tailTrace_6411772
  have hstable : (prefixWord ++ tailWord_6411772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411772).length < 2 ^ (prefixWord ++ tailWord_6411772).sum := by decide
  have hdescent : baseEnd_6411772 < baseStart_6411772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411786 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_6411786 : Nat := 118140960795 + 6411786 * 2 ^ 59
def prefixEnd_6411786 : Nat := 4983230072969 + 3 ^ 40 * 6411786 * 2
def baseEnd_6411786 : Nat := 365814230196550676831971

theorem tailTrace_6411786 : CollatzResearch.WordTrace tailWord_6411786 prefixEnd_6411786 365814230196550676831971 := by
  unfold tailWord_6411786
  simp only [CollatzResearch.WordTrace]
  refine ⟨58464261887300460678213803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155904698366134561808570141 58464261887300460678213803)
  ·
    refine ⟨87696392830950691017320705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58464261887300460678213803 87696392830950691017320705)
    ·
      refine ⟨65772294623213018262990529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87696392830950691017320705 65772294623213018262990529)
      ·
        refine ⟨49329220967409763697242897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65772294623213018262990529 49329220967409763697242897)
        ·
          refine ⟨36996915725557322772932173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49329220967409763697242897 36996915725557322772932173)
          ·
            refine ⟨13873843397083996039849565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36996915725557322772932173 13873843397083996039849565)
            ·
              refine ⟨5202691273906498514943587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13873843397083996039849565 5202691273906498514943587)
              ·
                refine ⟨7804036910859747772415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202691273906498514943587 7804036910859747772415381)
                ·
                  refine ⟨365814230196550676831971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7804036910859747772415381 365814230196550676831971)
                  ·
                    rfl

theorem cell23_6411786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_6411786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411786 prefixEnd_6411786 := by exact prefixLift 6411786
  have htrace : WordTrace (prefixWord ++ tailWord_6411786) baseStart_6411786 baseEnd_6411786 := by
    simpa [prefixWord, tailWord_6411786, baseEnd_6411786] using wordTrace_append hprefix tailTrace_6411786
  have hstable : (prefixWord ++ tailWord_6411786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411786).length < 2 ^ (prefixWord ++ tailWord_6411786).sum := by decide
  have hdescent : baseEnd_6411786 < baseStart_6411786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411839 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_6411839 : Nat := 118140960795 + 6411839 * 2 ^ 59
def prefixEnd_6411839 : Nat := 4983230072969 + 3 ^ 40 * 6411839 * 2
def baseEnd_6411839 : Nat := 3292355286243644384124995

theorem tailTrace_6411839 : CollatzResearch.WordTrace tailWord_6411839 prefixEnd_6411839 3292355286243644384124995 := by
  unfold tailWord_6411839
  simp only [CollatzResearch.WordTrace]
  refine ⟨233858980618009832764534571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155905987078673221843023047 233858980618009832764534571)
  ·
    refine ⟨350788470927014749146801857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233858980618009832764534571 350788470927014749146801857)
    ·
      refine ⟨263091353195261061860101393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350788470927014749146801857 263091353195261061860101393)
      ·
        refine ⟨197318514896445796395076045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263091353195261061860101393 197318514896445796395076045)
        ·
          refine ⟨73994443086167173648153517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197318514896445796395076045 73994443086167173648153517)
          ·
            refine ⟨27747916157312690118057569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73994443086167173648153517 27747916157312690118057569)
            ·
              refine ⟨20810937117984517588543177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27747916157312690118057569 20810937117984517588543177)
              ·
                refine ⟨15608202838488388191407383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20810937117984517588543177 15608202838488388191407383)
                ·
                  refine ⟨23412304257732582287111075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15608202838488388191407383 23412304257732582287111075)
                  ·
                    refine ⟨35118456386598873430666613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23412304257732582287111075 35118456386598873430666613)
                    ·
                      refine ⟨3292355286243644384124995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35118456386598873430666613 3292355286243644384124995)
                      ·
                        rfl

theorem cell23_6411839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_6411839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411839 prefixEnd_6411839 := by exact prefixLift 6411839
  have htrace : WordTrace (prefixWord ++ tailWord_6411839) baseStart_6411839 baseEnd_6411839 := by
    simpa [prefixWord, tailWord_6411839, baseEnd_6411839] using wordTrace_append hprefix tailTrace_6411839
  have hstable : (prefixWord ++ tailWord_6411839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411839).length < 2 ^ (prefixWord ++ tailWord_6411839).sum := by decide
  have hdescent : baseEnd_6411839 < baseStart_6411839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
