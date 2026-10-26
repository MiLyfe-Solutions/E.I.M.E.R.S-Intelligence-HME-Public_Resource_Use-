import V185TrunkScan23Chunk0725

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4294612 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4294612 : Nat := 118140960795 + 4294612 * 2 ^ 59
def prefixEnd_4294612 : Nat := 4983230072969 + 3 ^ 40 * 4294612 * 2
def baseEnd_4294612 : Nat := 2205200180566856544499445

theorem tailTrace_4294612 : CollatzResearch.WordTrace tailWord_4294612 prefixEnd_4294612 2205200180566856544499445 := by
  unfold tailWord_4294612
  simp only [CollatzResearch.WordTrace]
  refine ⟨78318683958680830090435045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104424911944907773453913393 78318683958680830090435045)
  ·
    refine ⟨14684753242252655641956571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78318683958680830090435045 14684753242252655641956571)
    ·
      refine ⟨22027129863378983462934857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14684753242252655641956571 22027129863378983462934857)
      ·
        refine ⟨16520347397534237597201143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22027129863378983462934857 16520347397534237597201143)
        ·
          refine ⟨24780521096301356395801715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16520347397534237597201143 24780521096301356395801715)
          ·
            refine ⟨37170781644452034593702573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24780521096301356395801715 37170781644452034593702573)
            ·
              refine ⟨13939043116669512972638465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37170781644452034593702573 13939043116669512972638465)
              ·
                refine ⟨10454282337502134729478849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13939043116669512972638465 10454282337502134729478849)
                ·
                  refine ⟨7840711753126601047109137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10454282337502134729478849 7840711753126601047109137)
                  ·
                    refine ⟨5880533814844950785331853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7840711753126601047109137 5880533814844950785331853)
                    ·
                      refine ⟨2205200180566856544499445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5880533814844950785331853 2205200180566856544499445)
                      ·
                        rfl

theorem cell23_4294612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4294612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294612 prefixEnd_4294612 := by exact prefixLift 4294612
  have htrace : WordTrace (prefixWord ++ tailWord_4294612) baseStart_4294612 baseEnd_4294612 := by
    simpa [prefixWord, tailWord_4294612, baseEnd_4294612] using wordTrace_append hprefix tailTrace_4294612
  have hstable : (prefixWord ++ tailWord_4294612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294612).length < 2 ^ (prefixWord ++ tailWord_4294612).sum := by decide
  have hdescent : baseEnd_4294612 < baseStart_4294612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294635 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 3, 5, 2]
def baseStart_4294635 : Nat := 118140960795 + 4294635 * 2 ^ 59
def prefixEnd_4294635 : Nat := 4983230072969 + 3 ^ 40 * 4294635 * 2
def baseEnd_4294635 : Nat := 2205211990621909954511839

theorem tailTrace_4294635 : CollatzResearch.WordTrace tailWord_4294635 prefixEnd_4294635 2205211990621909954511839 := by
  unfold tailWord_4294635
  simp only [CollatzResearch.WordTrace]
  refine ⟨156638206796278335108957359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104425471197518890072638239 156638206796278335108957359)
  ·
    refine ⟨234957310194417502663436039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156638206796278335108957359 234957310194417502663436039)
    ·
      refine ⟨352435965291626253995154059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234957310194417502663436039 352435965291626253995154059)
      ·
        refine ⟨528653947937439380992731089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352435965291626253995154059 528653947937439380992731089)
        ·
          refine ⟨396490460953079535744548317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528653947937439380992731089 396490460953079535744548317)
          ·
            refine ⟨148683922857404825904205619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396490460953079535744548317 148683922857404825904205619)
            ·
              refine ⟨223025884286107238856308429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148683922857404825904205619 223025884286107238856308429)
              ·
                refine ⟨83634706607290214571115661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223025884286107238856308429 83634706607290214571115661)
                ·
                  refine ⟨31363014977733830464168373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83634706607290214571115661 31363014977733830464168373)
                  ·
                    refine ⟨2940282654162546606015785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31363014977733830464168373 2940282654162546606015785)
                    ·
                      refine ⟨2205211990621909954511839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940282654162546606015785 2205211990621909954511839)
                      ·
                        rfl

theorem cell23_4294635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5, 2].length) (baseStart_4294635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294635 prefixEnd_4294635 := by exact prefixLift 4294635
  have htrace : WordTrace (prefixWord ++ tailWord_4294635) baseStart_4294635 baseEnd_4294635 := by
    simpa [prefixWord, tailWord_4294635, baseEnd_4294635] using wordTrace_append hprefix tailTrace_4294635
  have hstable : (prefixWord ++ tailWord_4294635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294635).length < 2 ^ (prefixWord ++ tailWord_4294635).sum := by decide
  have hdescent : baseEnd_4294635 < baseStart_4294635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294675 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 4, 4]
def baseStart_4294675 : Nat := 118140960795 + 4294675 * 2 ^ 59
def prefixEnd_4294675 : Nat := 4983230072969 + 3 ^ 40 * 4294675 * 2
def baseEnd_4294675 : Nat := 735077509949363266003885

theorem tailTrace_4294675 : CollatzResearch.WordTrace tailWord_4294675 prefixEnd_4294675 735077509949363266003885 := by
  unfold tailWord_4294675
  simp only [CollatzResearch.WordTrace]
  refine ⟨156639665716133421940413479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104426443810755614626942319 156639665716133421940413479)
  ·
    refine ⟨234959498574200132910620219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156639665716133421940413479 234959498574200132910620219)
    ·
      refine ⟨352439247861300199365930329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234959498574200132910620219 352439247861300199365930329)
      ·
        refine ⟨264329435895975149524447747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352439247861300199365930329 264329435895975149524447747)
        ·
          refine ⟨396494153843962724286671621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264329435895975149524447747 396494153843962724286671621)
          ·
            refine ⟨74342653845743010803750929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 396494153843962724286671621 74342653845743010803750929)
            ·
              refine ⟨55756990384307258102813197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74342653845743010803750929 55756990384307258102813197)
              ·
                refine ⟨20908871394115221788554949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55756990384307258102813197 20908871394115221788554949)
                ·
                  refine ⟨3920413386396604085354053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20908871394115221788554949 3920413386396604085354053)
                  ·
                    refine ⟨735077509949363266003885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920413386396604085354053 735077509949363266003885)
                    ·
                      rfl

theorem cell23_4294675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 4].length) (baseStart_4294675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294675 prefixEnd_4294675 := by exact prefixLift 4294675
  have htrace : WordTrace (prefixWord ++ tailWord_4294675) baseStart_4294675 baseEnd_4294675 := by
    simpa [prefixWord, tailWord_4294675, baseEnd_4294675] using wordTrace_append hprefix tailTrace_4294675
  have hstable : (prefixWord ++ tailWord_4294675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294675).length < 2 ^ (prefixWord ++ tailWord_4294675).sum := by decide
  have hdescent : baseEnd_4294675 < baseStart_4294675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294719 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 1, 2, 3]
def baseStart_4294719 : Nat := 118140960795 + 4294719 * 2 ^ 59
def prefixEnd_4294719 : Nat := 4983230072969 + 3 ^ 40 * 4294719 * 2
def baseEnd_4294719 : Nat := 2205255122996887625861453

theorem tailTrace_4294719 : CollatzResearch.WordTrace tailWord_4294719 prefixEnd_4294719 2205255122996887625861453 := by
  unfold tailWord_4294719
  simp only [CollatzResearch.WordTrace]
  refine ⟨156641270527974017455015211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104427513685316011636676807 156641270527974017455015211)
  ·
    refine ⟨234961905791961026182522817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156641270527974017455015211 234961905791961026182522817)
    ·
      refine ⟨176221429343970769636892113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234961905791961026182522817 176221429343970769636892113)
      ·
        refine ⟨132166072007978077227669085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176221429343970769636892113 132166072007978077227669085)
        ·
          refine ⟨49562277002991778960375907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132166072007978077227669085 49562277002991778960375907)
          ·
            refine ⟨74343415504487668440563861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49562277002991778960375907 74343415504487668440563861)
            ·
              refine ⟨3484847601772859458151431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74343415504487668440563861 3484847601772859458151431)
              ·
                refine ⟨5227271402659289187227147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484847601772859458151431 5227271402659289187227147)
                ·
                  refine ⟨7840907103988933780840721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5227271402659289187227147 7840907103988933780840721)
                  ·
                    refine ⟨5880680327991700335630541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7840907103988933780840721 5880680327991700335630541)
                    ·
                      refine ⟨2205255122996887625861453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5880680327991700335630541 2205255122996887625861453)
                      ·
                        rfl

theorem cell23_4294719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_4294719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294719 prefixEnd_4294719 := by exact prefixLift 4294719
  have htrace : WordTrace (prefixWord ++ tailWord_4294719) baseStart_4294719 baseEnd_4294719 := by
    simpa [prefixWord, tailWord_4294719, baseEnd_4294719] using wordTrace_append hprefix tailTrace_4294719
  have hstable : (prefixWord ++ tailWord_4294719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294719).length < 2 ^ (prefixWord ++ tailWord_4294719).sum := by decide
  have hdescent : baseEnd_4294719 < baseStart_4294719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294733 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_4294733 : Nat := 118140960795 + 4294733 * 2 ^ 59
def prefixEnd_4294733 : Nat := 4983230072969 + 3 ^ 40 * 4294733 * 2
def baseEnd_4294733 : Nat := 2205262311726050571086389

theorem tailTrace_4294733 : CollatzResearch.WordTrace tailWord_4294733 prefixEnd_4294733 2205262311726050571086389 := by
  unfold tailWord_4294733
  simp only [CollatzResearch.WordTrace]
  refine ⟨156641781149923297846024853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104427854099948865230683235 156641781149923297846024853)
  ·
    refine ⟨7342583491402654586532415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156641781149923297846024853 7342583491402654586532415)
    ·
      refine ⟨11013875237103981879798623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342583491402654586532415 11013875237103981879798623)
      ·
        refine ⟨16520812855655972819697935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11013875237103981879798623 16520812855655972819697935)
        ·
          refine ⟨24781219283483959229546903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16520812855655972819697935 24781219283483959229546903)
          ·
            refine ⟨37171828925225938844320355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24781219283483959229546903 37171828925225938844320355)
            ·
              refine ⟨55757743387838908266480533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37171828925225938844320355 55757743387838908266480533)
              ·
                refine ⟨2613644221304948824991275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55757743387838908266480533 2613644221304948824991275)
                ·
                  refine ⟨3920466331957423237486913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613644221304948824991275 3920466331957423237486913)
                  ·
                    refine ⟨2940349748968067428115185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3920466331957423237486913 2940349748968067428115185)
                    ·
                      refine ⟨2205262311726050571086389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940349748968067428115185 2205262311726050571086389)
                      ·
                        rfl

theorem cell23_4294733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_4294733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294733 prefixEnd_4294733 := by exact prefixLift 4294733
  have htrace : WordTrace (prefixWord ++ tailWord_4294733) baseStart_4294733 baseEnd_4294733 := by
    simpa [prefixWord, tailWord_4294733, baseEnd_4294733] using wordTrace_append hprefix tailTrace_4294733
  have hstable : (prefixWord ++ tailWord_4294733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294733).length < 2 ^ (prefixWord ++ tailWord_4294733).sum := by decide
  have hdescent : baseEnd_4294733 < baseStart_4294733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294755 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4]
def baseStart_4294755 : Nat := 118140960795 + 4294755 * 2 ^ 59
def prefixEnd_4294755 : Nat := 4983230072969 + 3 ^ 40 * 4294755 * 2
def baseEnd_4294755 : Nat := 2205273608300449485011287

theorem tailTrace_4294755 : CollatzResearch.WordTrace tailWord_4294755 prefixEnd_4294755 2205273608300449485011287 := by
  unfold tailWord_4294755
  simp only [CollatzResearch.WordTrace]
  refine ⟨156642583555843595603325719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104428389037229063735550479 156642583555843595603325719)
  ·
    refine ⟨234963875333765393404988579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156642583555843595603325719 234963875333765393404988579)
    ·
      refine ⟨352445813000648090107482869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234963875333765393404988579 352445813000648090107482869)
      ·
        refine ⟨33041794968810758447576519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 352445813000648090107482869 33041794968810758447576519)
        ·
          refine ⟨49562692453216137671364779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33041794968810758447576519 49562692453216137671364779)
          ·
            refine ⟨74344038679824206507047169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49562692453216137671364779 74344038679824206507047169)
            ·
              refine ⟨55758029009868154880285377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74344038679824206507047169 55758029009868154880285377)
              ·
                refine ⟨41818521757401116160214033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55758029009868154880285377 41818521757401116160214033)
                ·
                  refine ⟨31363891318050837120160525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41818521757401116160214033 31363891318050837120160525)
                  ·
                    refine ⟨11761459244269063920060197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31363891318050837120160525 11761459244269063920060197)
                    ·
                      refine ⟨2205273608300449485011287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11761459244269063920060197 2205273608300449485011287)
                      ·
                        rfl

theorem cell23_4294755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_4294755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294755 prefixEnd_4294755 := by exact prefixLift 4294755
  have htrace : WordTrace (prefixWord ++ tailWord_4294755) baseStart_4294755 baseEnd_4294755 := by
    simpa [prefixWord, tailWord_4294755, baseEnd_4294755] using wordTrace_append hprefix tailTrace_4294755
  have hstable : (prefixWord ++ tailWord_4294755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294755).length < 2 ^ (prefixWord ++ tailWord_4294755).sum := by decide
  have hdescent : baseEnd_4294755 < baseStart_4294755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294775 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_4294775 : Nat := 118140960795 + 4294775 * 2 ^ 59
def prefixEnd_4294775 : Nat := 4983230072969 + 3 ^ 40 * 4294775 * 2
def baseEnd_4294775 : Nat := 2205283877913539406761195

theorem tailTrace_4294775 : CollatzResearch.WordTrace tailWord_4294775 prefixEnd_4294775 2205283877913539406761195 := by
  unfold tailWord_4294775
  simp only [CollatzResearch.WordTrace]
  refine ⟨156643313015771139019053779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104428875343847426012702519 156643313015771139019053779)
  ·
    refine ⟨234964969523656708528580669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156643313015771139019053779 234964969523656708528580669)
    ·
      refine ⟨88111863571371265698217751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234964969523656708528580669 88111863571371265698217751)
      ·
        refine ⟨132167795357056898547326627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88111863571371265698217751 132167795357056898547326627)
        ·
          refine ⟨198251693035585347820989941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132167795357056898547326627 198251693035585347820989941)
          ·
            refine ⟨18586096222086126358217807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198251693035585347820989941 18586096222086126358217807)
            ·
              refine ⟨27879144333129189537326711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18586096222086126358217807 27879144333129189537326711)
              ·
                refine ⟨41818716499693784305990067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27879144333129189537326711 41818716499693784305990067)
                ·
                  refine ⟨62728074749540676458985101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41818716499693784305990067 62728074749540676458985101)
                  ·
                    refine ⟨23523028031077753672119413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62728074749540676458985101 23523028031077753672119413)
                    ·
                      refine ⟨2205283877913539406761195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23523028031077753672119413 2205283877913539406761195)
                      ·
                        rfl

theorem cell23_4294775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_4294775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294775 prefixEnd_4294775 := by exact prefixLift 4294775
  have htrace : WordTrace (prefixWord ++ tailWord_4294775) baseStart_4294775 baseEnd_4294775 := by
    simpa [prefixWord, tailWord_4294775, baseEnd_4294775] using wordTrace_append hprefix tailTrace_4294775
  have hstable : (prefixWord ++ tailWord_4294775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294775).length < 2 ^ (prefixWord ++ tailWord_4294775).sum := by decide
  have hdescent : baseEnd_4294775 < baseStart_4294775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294802 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4294802 : Nat := 118140960795 + 4294802 * 2 ^ 59
def prefixEnd_4294802 : Nat := 4983230072969 + 3 ^ 40 * 4294802 * 2
def baseEnd_4294802 : Nat := 2205297741891210801123571

theorem tailTrace_4294802 : CollatzResearch.WordTrace tailWord_4294802 prefixEnd_4294802 2205297741891210801123571 := by
  unfold tailWord_4294802
  simp only [CollatzResearch.WordTrace]
  refine ⟨39161074446668330657571665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104429531857782215086857773 39161074446668330657571665)
  ·
    refine ⟨29370805835001247993178749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39161074446668330657571665 29370805835001247993178749)
    ·
      refine ⟨11014052188125467997442031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29370805835001247993178749 11014052188125467997442031)
      ·
        refine ⟨16521078282188201996163047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11014052188125467997442031 16521078282188201996163047)
        ·
          refine ⟨24781617423282302994244571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16521078282188201996163047 24781617423282302994244571)
          ·
            refine ⟨37172426134923454491366857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24781617423282302994244571 37172426134923454491366857)
            ·
              refine ⟨27879319601192590868525143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37172426134923454491366857 27879319601192590868525143)
              ·
                refine ⟨41818979401788886302787715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27879319601192590868525143 41818979401788886302787715)
                ·
                  refine ⟨62728469102683329454181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41818979401788886302787715 62728469102683329454181573)
                  ·
                    refine ⟨11761587956753124272659045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62728469102683329454181573 11761587956753124272659045)
                    ·
                      refine ⟨2205297741891210801123571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11761587956753124272659045 2205297741891210801123571)
                      ·
                        rfl

theorem cell23_4294802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4294802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294802 prefixEnd_4294802 := by exact prefixLift 4294802
  have htrace : WordTrace (prefixWord ++ tailWord_4294802) baseStart_4294802 baseEnd_4294802 := by
    simpa [prefixWord, tailWord_4294802, baseEnd_4294802] using wordTrace_append hprefix tailTrace_4294802
  have hstable : (prefixWord ++ tailWord_4294802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294802).length < 2 ^ (prefixWord ++ tailWord_4294802).sum := by decide
  have hdescent : baseEnd_4294802 < baseStart_4294802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294810 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4294810 : Nat := 118140960795 + 4294810 * 2 ^ 59
def prefixEnd_4294810 : Nat := 4983230072969 + 3 ^ 40 * 4294810 * 2
def baseEnd_4294810 : Nat := 2205301849736446769823535

theorem tailTrace_4294810 : CollatzResearch.WordTrace tailWord_4294810 prefixEnd_4294810 2205301849736446769823535 := by
  unfold tailWord_4294810
  simp only [CollatzResearch.WordTrace]
  refine ⟨39161147392661084999144471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104429726380429559997718589 39161147392661084999144471)
  ·
    refine ⟨58741721088991627498716707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39161147392661084999144471 58741721088991627498716707)
    ·
      refine ⟨88112581633487441248075061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58741721088991627498716707 88112581633487441248075061)
      ·
        refine ⟨8260554528139447617007037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88112581633487441248075061 8260554528139447617007037)
        ·
          refine ⟨3097707948052292856377639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8260554528139447617007037 3097707948052292856377639)
          ·
            refine ⟨4646561922078439284566459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097707948052292856377639 4646561922078439284566459)
            ·
              refine ⟨6969842883117658926849689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4646561922078439284566459 6969842883117658926849689)
              ·
                refine ⟨5227382162338244195137267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6969842883117658926849689 5227382162338244195137267)
                ·
                  refine ⟨7841073243507366292705901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5227382162338244195137267 7841073243507366292705901)
                  ·
                    refine ⟨2940402466315262359764713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7841073243507366292705901 2940402466315262359764713)
                    ·
                      refine ⟨2205301849736446769823535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940402466315262359764713 2205301849736446769823535)
                      ·
                        rfl

theorem cell23_4294810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4294810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294810 prefixEnd_4294810 := by exact prefixLift 4294810
  have htrace : WordTrace (prefixWord ++ tailWord_4294810) baseStart_4294810 baseEnd_4294810 := by
    simpa [prefixWord, tailWord_4294810, baseEnd_4294810] using wordTrace_append hprefix tailTrace_4294810
  have hstable : (prefixWord ++ tailWord_4294810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294810).length < 2 ^ (prefixWord ++ tailWord_4294810).sum := by decide
  have hdescent : baseEnd_4294810 < baseStart_4294810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294832 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 7, 2]
def baseStart_4294832 : Nat := 118140960795 + 4294832 * 2 ^ 59
def prefixEnd_4294832 : Nat := 4983230072969 + 3 ^ 40 * 4294832 * 2
def baseEnd_4294832 : Nat := 2205313146310845683748433

theorem tailTrace_4294832 : CollatzResearch.WordTrace tailWord_4294832 prefixEnd_4294832 2205313146310845683748433 := by
  unfold tailWord_4294832
  simp only [CollatzResearch.WordTrace]
  refine ⟨78322695988282318876939375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104430261317709758502585833 78322695988282318876939375)
  ·
    refine ⟨117484043982423478315409063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78322695988282318876939375 117484043982423478315409063)
    ·
      refine ⟨176226065973635217473113595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117484043982423478315409063 176226065973635217473113595)
      ·
        refine ⟨264339098960452826209670393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176226065973635217473113595 264339098960452826209670393)
        ·
          refine ⟨198254324220339619657252795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264339098960452826209670393 198254324220339619657252795)
          ·
            refine ⟨297381486330509429485879193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198254324220339619657252795 297381486330509429485879193)
            ·
              refine ⟨223036114747882072114409395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297381486330509429485879193 223036114747882072114409395)
              ·
                refine ⟨334554172121823108171614093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223036114747882072114409395 334554172121823108171614093)
                ·
                  refine ⟨125457814545683665564355285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334554172121823108171614093 125457814545683665564355285)
                  ·
                    refine ⟨2940417528414460911664577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 125457814545683665564355285 2940417528414460911664577)
                    ·
                      refine ⟨2205313146310845683748433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940417528414460911664577 2205313146310845683748433)
                      ·
                        rfl

theorem cell23_4294832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 7, 2].length) (baseStart_4294832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294832 prefixEnd_4294832 := by exact prefixLift 4294832
  have htrace : WordTrace (prefixWord ++ tailWord_4294832) baseStart_4294832 baseEnd_4294832 := by
    simpa [prefixWord, tailWord_4294832, baseEnd_4294832] using wordTrace_append hprefix tailTrace_4294832
  have hstable : (prefixWord ++ tailWord_4294832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294832).length < 2 ^ (prefixWord ++ tailWord_4294832).sum := by decide
  have hdescent : baseEnd_4294832 < baseStart_4294832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294842 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_4294842 : Nat := 118140960795 + 4294842 * 2 ^ 59
def prefixEnd_4294842 : Nat := 4983230072969 + 3 ^ 40 * 4294842 * 2
def baseEnd_4294842 : Nat := 735106093705796881541129

theorem tailTrace_4294842 : CollatzResearch.WordTrace tailWord_4294842 prefixEnd_4294842 735106093705796881541129 := by
  unfold tailWord_4294842
  simp only [CollatzResearch.WordTrace]
  refine ⟨39161439176632102365435695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104430504471018939641161853 39161439176632102365435695)
  ·
    refine ⟨58742158764948153548153543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39161439176632102365435695 58742158764948153548153543)
    ·
      refine ⟨88113238147422230322230315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58742158764948153548153543 88113238147422230322230315)
      ·
        refine ⟨132169857221133345483345473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88113238147422230322230315 132169857221133345483345473)
        ·
          refine ⟨99127392915850009112509105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132169857221133345483345473 99127392915850009112509105)
          ·
            refine ⟨74345544686887506834381829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99127392915850009112509105 74345544686887506834381829)
            ·
              refine ⟨13939789628791407531446593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74345544686887506834381829 13939789628791407531446593)
              ·
                refine ⟨10454842221593555648584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13939789628791407531446593 10454842221593555648584945)
                ·
                  refine ⟨7841131666195166736438709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10454842221593555648584945 7841131666195166736438709)
                  ·
                    refine ⟨735106093705796881541129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7841131666195166736438709 735106093705796881541129)
                    ·
                      rfl

theorem cell23_4294842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_4294842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294842 prefixEnd_4294842 := by exact prefixLift 4294842
  have htrace : WordTrace (prefixWord ++ tailWord_4294842) baseStart_4294842 baseEnd_4294842 := by
    simpa [prefixWord, tailWord_4294842, baseEnd_4294842] using wordTrace_append hprefix tailTrace_4294842
  have hstable : (prefixWord ++ tailWord_4294842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294842).length < 2 ^ (prefixWord ++ tailWord_4294842).sum := by decide
  have hdescent : baseEnd_4294842 < baseStart_4294842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294846 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_4294846 : Nat := 118140960795 + 4294846 * 2 ^ 59
def prefixEnd_4294846 : Nat := 4983230072969 + 3 ^ 40 * 4294846 * 2
def baseEnd_4294846 : Nat := 245035592782223180997041

theorem tailTrace_4294846 : CollatzResearch.WordTrace tailWord_4294846 prefixEnd_4294846 245035592782223180997041 := by
  unfold tailWord_4294846
  simp only [CollatzResearch.WordTrace]
  refine ⟨19580737824814239768111049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104430601732342612096592261 19580737824814239768111049)
  ·
    refine ⟨14685553368610679826083287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19580737824814239768111049 14685553368610679826083287)
    ·
      refine ⟨22028330052916019739124931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14685553368610679826083287 22028330052916019739124931)
      ·
        refine ⟨33042495079374029608687397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22028330052916019739124931 33042495079374029608687397)
        ·
          refine ⟨6195467827382630551628887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33042495079374029608687397 6195467827382630551628887)
          ·
            refine ⟨9293201741073945827443331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195467827382630551628887 9293201741073945827443331)
            ·
              refine ⟨13939802611610918741164997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9293201741073945827443331 13939802611610918741164997)
              ·
                refine ⟨2613712989677047263968437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13939802611610918741164997 2613712989677047263968437)
                ·
                  refine ⟨245035592782223180997041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2613712989677047263968437 245035592782223180997041)
                  ·
                    rfl

theorem cell23_4294846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_4294846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294846 prefixEnd_4294846 := by exact prefixLift 4294846
  have htrace : WordTrace (prefixWord ++ tailWord_4294846) baseStart_4294846 baseEnd_4294846 := by
    simpa [prefixWord, tailWord_4294846, baseEnd_4294846] using wordTrace_append hprefix tailTrace_4294846
  have hstable : (prefixWord ++ tailWord_4294846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294846).length < 2 ^ (prefixWord ++ tailWord_4294846).sum := by decide
  have hdescent : baseEnd_4294846 < baseStart_4294846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294855 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 8]
def baseStart_4294855 : Nat := 118140960795 + 4294855 * 2 ^ 59
def prefixEnd_4294855 : Nat := 4983230072969 + 3 ^ 40 * 4294855 * 2
def baseEnd_4294855 : Nat := 735108318788633031253609

theorem tailTrace_4294855 : CollatzResearch.WordTrace tailWord_4294855 prefixEnd_4294855 735108318788633031253609 := by
  unfold tailWord_4294855
  simp only [CollatzResearch.WordTrace]
  refine ⟨156646230855481312681966019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104430820570320875121310679 156646230855481312681966019)
  ·
    refine ⟨234969346283221969022949029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156646230855481312681966019 234969346283221969022949029)
    ·
      refine ⟨44056752428104119191802943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234969346283221969022949029 44056752428104119191802943)
      ·
        refine ⟨66085128642156178787704415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44056752428104119191802943 66085128642156178787704415)
        ·
          refine ⟨99127692963234268181556623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66085128642156178787704415 99127692963234268181556623)
          ·
            refine ⟨148691539444851402272334935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99127692963234268181556623 148691539444851402272334935)
            ·
              refine ⟨223037309167277103408502403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148691539444851402272334935 223037309167277103408502403)
              ·
                refine ⟨334555963750915655112753605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223037309167277103408502403 334555963750915655112753605)
                ·
                  refine ⟨62729243203296685333641301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334555963750915655112753605 62729243203296685333641301)
                  ·
                    refine ⟨735108318788633031253609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62729243203296685333641301 735108318788633031253609)
                    ·
                      rfl

theorem cell23_4294855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_4294855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294855 prefixEnd_4294855 := by exact prefixLift 4294855
  have htrace : WordTrace (prefixWord ++ tailWord_4294855) baseStart_4294855 baseEnd_4294855 := by
    simpa [prefixWord, tailWord_4294855, baseEnd_4294855] using wordTrace_append hprefix tailTrace_4294855
  have hstable : (prefixWord ++ tailWord_4294855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294855).length < 2 ^ (prefixWord ++ tailWord_4294855).sum := by decide
  have hdescent : baseEnd_4294855 < baseStart_4294855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294875 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_4294875 : Nat := 118140960795 + 4294875 * 2 ^ 59
def prefixEnd_4294875 : Nat := 4983230072969 + 3 ^ 40 * 4294875 * 2
def baseEnd_4294875 : Nat := 2205335225978989015510735

theorem tailTrace_4294875 : CollatzResearch.WordTrace tailWord_4294875 prefixEnd_4294875 2205335225978989015510735 := by
  unfold tailWord_4294875
  simp only [CollatzResearch.WordTrace]
  refine ⟨156646960315408856097694079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104431306876939237398462719 156646960315408856097694079)
  ·
    refine ⟨234970440473113284146541119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156646960315408856097694079 234970440473113284146541119)
    ·
      refine ⟨352455660709669926219811679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234970440473113284146541119 352455660709669926219811679)
      ·
        refine ⟨528683491064504889329717519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352455660709669926219811679 528683491064504889329717519)
        ·
          refine ⟨793025236596757333994576279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528683491064504889329717519 793025236596757333994576279)
          ·
            refine ⟨1189537854895136000991864419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793025236596757333994576279 1189537854895136000991864419)
            ·
              refine ⟨1784306782342704001487796629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189537854895136000991864419 1784306782342704001487796629)
              ·
                refine ⟨83639380422314250069740467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1784306782342704001487796629 83639380422314250069740467)
                ·
                  refine ⟨125459070633471375104610701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83639380422314250069740467 125459070633471375104610701)
                  ·
                    refine ⟨47047151487551765664229013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125459070633471375104610701 47047151487551765664229013)
                    ·
                      refine ⟨2205335225978989015510735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47047151487551765664229013 2205335225978989015510735)
                      ·
                        rfl

theorem cell23_4294875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_4294875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294875 prefixEnd_4294875 := by exact prefixLift 4294875
  have htrace : WordTrace (prefixWord ++ tailWord_4294875) baseStart_4294875 baseEnd_4294875 := by
    simpa [prefixWord, tailWord_4294875, baseEnd_4294875] using wordTrace_append hprefix tailTrace_4294875
  have hstable : (prefixWord ++ tailWord_4294875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294875).length < 2 ^ (prefixWord ++ tailWord_4294875).sum := by decide
  have hdescent : baseEnd_4294875 < baseStart_4294875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294876 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4294876 : Nat := 118140960795 + 4294876 * 2 ^ 59
def prefixEnd_4294876 : Nat := 4983230072969 + 3 ^ 40 * 4294876 * 2
def baseEnd_4294876 : Nat := 735111913153214503866077

theorem tailTrace_4294876 : CollatzResearch.WordTrace tailWord_4294876 prefixEnd_4294876 735111913153214503866077 := by
  unfold tailWord_4294876
  simp only [CollatzResearch.WordTrace]
  refine ⟨78323498394202616634240241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104431331192270155512320321 78323498394202616634240241)
  ·
    refine ⟨58742623795651962475680181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78323498394202616634240241 58742623795651962475680181)
    ·
      refine ⟨5507120980842371482095017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58742623795651962475680181 5507120980842371482095017)
      ·
        refine ⟨4130340735631778611571263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5507120980842371482095017 4130340735631778611571263)
        ·
          refine ⟨6195511103447667917356895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4130340735631778611571263 6195511103447667917356895)
          ·
            refine ⟨9293266655171501876035343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195511103447667917356895 9293266655171501876035343)
            ·
              refine ⟨13939899982757252814053015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9293266655171501876035343 13939899982757252814053015)
              ·
                refine ⟨20909849974135879221079523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13939899982757252814053015 20909849974135879221079523)
                ·
                  refine ⟨31364774961203818831619285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20909849974135879221079523 31364774961203818831619285)
                  ·
                    refine ⟨735111913153214503866077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31364774961203818831619285 735111913153214503866077)
                    ·
                      rfl

theorem cell23_4294876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4294876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294876 prefixEnd_4294876 := by exact prefixLift 4294876
  have htrace : WordTrace (prefixWord ++ tailWord_4294876) baseStart_4294876 baseEnd_4294876 := by
    simpa [prefixWord, tailWord_4294876, baseEnd_4294876] using wordTrace_append hprefix tailTrace_4294876
  have hstable : (prefixWord ++ tailWord_4294876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294876).length < 2 ^ (prefixWord ++ tailWord_4294876).sum := by decide
  have hdescent : baseEnd_4294876 < baseStart_4294876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294906 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_4294906 : Nat := 118140960795 + 4294906 * 2 ^ 59
def prefixEnd_4294906 : Nat := 4983230072969 + 3 ^ 40 * 4294906 * 2
def baseEnd_4294906 : Nat := 735117047959759464741031

theorem tailTrace_4294906 : CollatzResearch.WordTrace tailWord_4294906 prefixEnd_4294906 735117047959759464741031 := by
  unfold tailWord_4294906
  simp only [CollatzResearch.WordTrace]
  refine ⟨39162022744574137098018143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104432060652197698928048381 39162022744574137098018143)
  ·
    refine ⟨58743034116861205647027215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39162022744574137098018143 58743034116861205647027215)
    ·
      refine ⟨88114551175291808470540823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58743034116861205647027215 88114551175291808470540823)
      ·
        refine ⟨132171826762937712705811235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88114551175291808470540823 132171826762937712705811235)
        ·
          refine ⟨198257740144406569058716853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132171826762937712705811235 198257740144406569058716853)
          ·
            refine ⟨18586663138538115849254705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198257740144406569058716853 18586663138538115849254705)
            ·
              refine ⟨13939997353903586886941029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18586663138538115849254705 13939997353903586886941029)
              ·
                refine ⟨2613749503856922541301443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13939997353903586886941029 2613749503856922541301443)
                ·
                  refine ⟨3920624255785383811952165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613749503856922541301443 3920624255785383811952165)
                  ·
                    refine ⟨735117047959759464741031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920624255785383811952165 735117047959759464741031)
                    ·
                      rfl

theorem cell23_4294906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_4294906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294906 prefixEnd_4294906 := by exact prefixLift 4294906
  have htrace : WordTrace (prefixWord ++ tailWord_4294906) baseStart_4294906 baseEnd_4294906 := by
    simpa [prefixWord, tailWord_4294906, baseEnd_4294906] using wordTrace_append hprefix tailTrace_4294906
  have hstable : (prefixWord ++ tailWord_4294906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294906).length < 2 ^ (prefixWord ++ tailWord_4294906).sum := by decide
  have hdescent : baseEnd_4294906 < baseStart_4294906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294939 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 1, 5, 2]
def baseStart_4294939 : Nat := 118140960795 + 4294939 * 2 ^ 59
def prefixEnd_4294939 : Nat := 4983230072969 + 3 ^ 40 * 4294939 * 2
def baseEnd_4294939 : Nat := 2205368088740876765110441

theorem tailTrace_4294939 : CollatzResearch.WordTrace tailWord_4294939 prefixEnd_4294939 2205368088740876765110441 := by
  unfold tailWord_4294939
  simp only [CollatzResearch.WordTrace]
  refine ⟨156649294587176995028023871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104432863058117996685349247 156649294587176995028023871)
  ·
    refine ⟨234973941880765492542035807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156649294587176995028023871 234973941880765492542035807)
    ·
      refine ⟨352460912821148238813053711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234973941880765492542035807 352460912821148238813053711)
      ·
        refine ⟨528691369231722358219580567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352460912821148238813053711 528691369231722358219580567)
        ·
          refine ⟨793037053847583537329370851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528691369231722358219580567 793037053847583537329370851)
          ·
            refine ⟨1189555580771375305994056277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793037053847583537329370851 1189555580771375305994056277)
            ·
              refine ⟨13940104462164554367117847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1189555580771375305994056277 13940104462164554367117847)
              ·
                refine ⟨20910156693246831550676771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13940104462164554367117847 20910156693246831550676771)
                ·
                  refine ⟨31365235039870247326015157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20910156693246831550676771 31365235039870247326015157)
                  ·
                    refine ⟨2940490784987835686813921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31365235039870247326015157 2940490784987835686813921)
                    ·
                      refine ⟨2205368088740876765110441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940490784987835686813921 2205368088740876765110441)
                      ·
                        rfl

theorem cell23_4294939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5, 2].length) (baseStart_4294939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294939 prefixEnd_4294939 := by exact prefixLift 4294939
  have htrace : WordTrace (prefixWord ++ tailWord_4294939) baseStart_4294939 baseEnd_4294939 := by
    simpa [prefixWord, tailWord_4294939, baseEnd_4294939] using wordTrace_append hprefix tailTrace_4294939
  have hstable : (prefixWord ++ tailWord_4294939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294939).length < 2 ^ (prefixWord ++ tailWord_4294939).sum := by decide
  have hdescent : baseEnd_4294939 < baseStart_4294939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294957 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4294957 : Nat := 118140960795 + 4294957 * 2 ^ 59
def prefixEnd_4294957 : Nat := 4983230072969 + 3 ^ 40 * 4294957 * 2
def baseEnd_4294957 : Nat := 735125777130885898228453

theorem tailTrace_4294957 : CollatzResearch.WordTrace tailWord_4294957 prefixEnd_4294957 735125777130885898228453 := by
  unfold tailWord_4294957
  simp only [CollatzResearch.WordTrace]
  refine ⟨156649951101111784102179125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104433300734074522734786083 156649951101111784102179125)
  ·
    refine ⟨14685932915729229759579293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156649951101111784102179125 14685932915729229759579293)
    ·
      refine ⟨5507224843398461159842235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14685932915729229759579293 5507224843398461159842235)
      ·
        refine ⟨8260837265097691739763353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5507224843398461159842235 8260837265097691739763353)
        ·
          refine ⟨6195627948823268804822515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8260837265097691739763353 6195627948823268804822515)
          ·
            refine ⟨9293441923234903207233773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195627948823268804822515 9293441923234903207233773)
            ·
              refine ⟨3485040721213088702712665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9293441923234903207233773 3485040721213088702712665)
              ·
                refine ⟨2613780540909816527034499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485040721213088702712665 2613780540909816527034499)
                ·
                  refine ⟨3920670811364724790551749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613780540909816527034499 3920670811364724790551749)
                  ·
                    refine ⟨735125777130885898228453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920670811364724790551749 735125777130885898228453)
                    ·
                      rfl

theorem cell23_4294957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4294957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294957 prefixEnd_4294957 := by exact prefixLift 4294957
  have htrace : WordTrace (prefixWord ++ tailWord_4294957) baseStart_4294957 baseEnd_4294957 := by
    simpa [prefixWord, tailWord_4294957, baseEnd_4294957] using wordTrace_append hprefix tailTrace_4294957
  have hstable : (prefixWord ++ tailWord_4294957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294957).length < 2 ^ (prefixWord ++ tailWord_4294957).sum := by decide
  have hdescent : baseEnd_4294957 < baseStart_4294957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294992 : List Nat := [2, 1, 1, 1, 1, 6, 2, 9]
def baseStart_4294992 : Nat := 118140960795 + 4294992 * 2 ^ 59
def prefixEnd_4294992 : Nat := 4983230072969 + 3 ^ 40 * 4294992 * 2
def baseEnd_4294992 : Nat := 81681307526502409546211

theorem tailTrace_4294992 : CollatzResearch.WordTrace tailWord_4294992 prefixEnd_4294992 81681307526502409546211 := by
  unfold tailWord_4294992
  simp only [CollatzResearch.WordTrace]
  refine ⟨78325613827992492539851615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104434151770656656719802153 78325613827992492539851615)
  ·
    refine ⟨117488420741988738809777423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78325613827992492539851615 117488420741988738809777423)
    ·
      refine ⟨176232631112983108214666135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117488420741988738809777423 176232631112983108214666135)
      ·
        refine ⟨264348946669474662321999203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176232631112983108214666135 264348946669474662321999203)
        ·
          refine ⟨396523420004211993482998805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264348946669474662321999203 396523420004211993482998805)
          ·
            refine ⟨18587035312697437194515569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 396523420004211993482998805 18587035312697437194515569)
            ·
              refine ⟨13940276484523077895886677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18587035312697437194515569 13940276484523077895886677)
              ·
                refine ⟨81681307526502409546211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13940276484523077895886677 81681307526502409546211)
                ·
                  rfl

theorem cell23_4294992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 9].length) (baseStart_4294992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294992 prefixEnd_4294992 := by exact prefixLift 4294992
  have htrace : WordTrace (prefixWord ++ tailWord_4294992) baseStart_4294992 baseEnd_4294992 := by
    simpa [prefixWord, tailWord_4294992, baseEnd_4294992] using wordTrace_append hprefix tailTrace_4294992
  have hstable : (prefixWord ++ tailWord_4294992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294992).length < 2 ^ (prefixWord ++ tailWord_4294992).sum := by decide
  have hdescent : baseEnd_4294992 < baseStart_4294992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294999 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_4294999 : Nat := 118140960795 + 4294999 * 2 ^ 59
def prefixEnd_4294999 : Nat := 4983230072969 + 3 ^ 40 * 4294999 * 2
def baseEnd_4294999 : Nat := 2205398897580146530360165

theorem tailTrace_4294999 : CollatzResearch.WordTrace tailWord_4294999 prefixEnd_4294999 2205398897580146530360165 := by
  unfold tailWord_4294999
  simp only [CollatzResearch.WordTrace]
  refine ⟨156651482966959625275208051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104434321977973083516805367 156651482966959625275208051)
  ·
    refine ⟨234977224450439437912812077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156651482966959625275208051 234977224450439437912812077)
    ·
      refine ⟨88116459168914789217304529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234977224450439437912812077 88116459168914789217304529)
      ·
        refine ⟨66087344376686091912978397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88116459168914789217304529 66087344376686091912978397)
        ·
          refine ⟨24782754141257284467366899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66087344376686091912978397 24782754141257284467366899)
          ·
            refine ⟨37174131211885926701050349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24782754141257284467366899 37174131211885926701050349)
            ·
              refine ⟨13940299204457222512893881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37174131211885926701050349 13940299204457222512893881)
              ·
                refine ⟨10455224403342916884670411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13940299204457222512893881 10455224403342916884670411)
                ·
                  refine ⟨15682836605014375327005617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10455224403342916884670411 15682836605014375327005617)
                  ·
                    refine ⟨11762127453760781495254213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15682836605014375327005617 11762127453760781495254213)
                    ·
                      refine ⟨2205398897580146530360165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11762127453760781495254213 2205398897580146530360165)
                      ·
                        rfl

theorem cell23_4294999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_4294999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294999 prefixEnd_4294999 := by exact prefixLift 4294999
  have htrace : WordTrace (prefixWord ++ tailWord_4294999) baseStart_4294999 baseEnd_4294999 := by
    simpa [prefixWord, tailWord_4294999, baseEnd_4294999] using wordTrace_append hprefix tailTrace_4294999
  have hstable : (prefixWord ++ tailWord_4294999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294999).length < 2 ^ (prefixWord ++ tailWord_4294999).sum := by decide
  have hdescent : baseEnd_4294999 < baseStart_4294999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295070 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4295070 : Nat := 118140960795 + 4295070 * 2 ^ 59
def prefixEnd_4295070 : Nat := 4983230072969 + 3 ^ 40 * 4295070 * 2
def baseEnd_4295070 : Nat := 2205435354706615752572339

theorem tailTrace_4295070 : CollatzResearch.WordTrace tailWord_4295070 prefixEnd_4295070 2205435354706615752572339 := by
  unfold tailWord_4295070
  simp only [CollatzResearch.WordTrace]
  refine ⟨19581759068712800550130333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104436048366468269600695109 19581759068712800550130333)
  ·
    refine ⟨7343159650767300206298875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19581759068712800550130333 7343159650767300206298875)
    ·
      refine ⟨11014739476150950309448313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7343159650767300206298875 11014739476150950309448313)
      ·
        refine ⟨8261054607113212732086235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11014739476150950309448313 8261054607113212732086235)
        ·
          refine ⟨12391581910669819098129353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8261054607113212732086235 12391581910669819098129353)
          ·
            refine ⟨9293686433002364323597015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12391581910669819098129353 9293686433002364323597015)
            ·
              refine ⟨13940529649503546485395523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9293686433002364323597015 13940529649503546485395523)
              ·
                refine ⟨20910794474255319728093285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13940529649503546485395523 20910794474255319728093285)
                ·
                  refine ⟨3920773963922872449017491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20910794474255319728093285 3920773963922872449017491)
                  ·
                    refine ⟨5881160945884308673526237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3920773963922872449017491 5881160945884308673526237)
                    ·
                      refine ⟨2205435354706615752572339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5881160945884308673526237 2205435354706615752572339)
                      ·
                        rfl

theorem cell23_4295070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4295070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295070 prefixEnd_4295070 := by exact prefixLift 4295070
  have htrace : WordTrace (prefixWord ++ tailWord_4295070) baseStart_4295070 baseEnd_4295070 := by
    simpa [prefixWord, tailWord_4295070, baseEnd_4295070] using wordTrace_append hprefix tailTrace_4295070
  have hstable : (prefixWord ++ tailWord_4295070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295070).length < 2 ^ (prefixWord ++ tailWord_4295070).sum := by decide
  have hdescent : baseEnd_4295070 < baseStart_4295070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295076 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_4295076 : Nat := 118140960795 + 4295076 * 2 ^ 59
def prefixEnd_4295076 : Nat := 4983230072969 + 3 ^ 40 * 4295076 * 2
def baseEnd_4295076 : Nat := 2205438435590542729097311

theorem tailTrace_4295076 : CollatzResearch.WordTrace tailWord_4295076 prefixEnd_4295076 2205438435590542729097311 := by
  unfold tailWord_4295076
  simp only [CollatzResearch.WordTrace]
  refine ⟨78327145693840333712880541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104436194258453778283840721 78327145693840333712880541)
  ·
    refine ⟨29372679635190125142330203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78327145693840333712880541 29372679635190125142330203)
    ·
      refine ⟨44059019452785187713495305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29372679635190125142330203 44059019452785187713495305)
      ·
        refine ⟨33044264589588890785121479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44059019452785187713495305 33044264589588890785121479)
        ·
          refine ⟨49566396884383336177682219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33044264589588890785121479 49566396884383336177682219)
          ·
            refine ⟨74349595326575004266523329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49566396884383336177682219 74349595326575004266523329)
            ·
              refine ⟨55762196494931253199892497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74349595326575004266523329 55762196494931253199892497)
              ·
                refine ⟨41821647371198439899919373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55762196494931253199892497 41821647371198439899919373)
                ·
                  refine ⟨15683117764199414962469765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41821647371198439899919373 15683117764199414962469765)
                  ·
                    refine ⟨2940584580787390305463081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15683117764199414962469765 2940584580787390305463081)
                    ·
                      refine ⟨2205438435590542729097311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940584580787390305463081 2205438435590542729097311)
                      ·
                        rfl

theorem cell23_4295076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_4295076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295076 prefixEnd_4295076 := by exact prefixLift 4295076
  have htrace : WordTrace (prefixWord ++ tailWord_4295076) baseStart_4295076 baseEnd_4295076 := by
    simpa [prefixWord, tailWord_4295076, baseEnd_4295076] using wordTrace_append hprefix tailTrace_4295076
  have hstable : (prefixWord ++ tailWord_4295076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295076).length < 2 ^ (prefixWord ++ tailWord_4295076).sum := by decide
  have hdescent : baseEnd_4295076 < baseStart_4295076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295126 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4295126 : Nat := 118140960795 + 4295126 * 2 ^ 59
def prefixEnd_4295126 : Nat := 4983230072969 + 3 ^ 40 * 4295126 * 2
def baseEnd_4295126 : Nat := 2205464109623267533472081

theorem tailTrace_4295126 : CollatzResearch.WordTrace tailWord_4295126 prefixEnd_4295126 2205464109623267533472081 := by
  unfold tailWord_4295126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791007189843720372817577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104437410024999683976720821 9791007189843720372817577)
  ·
    refine ⟨7343255392382790279613183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9791007189843720372817577 7343255392382790279613183)
    ·
      refine ⟨11014883088574185419419775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7343255392382790279613183 11014883088574185419419775)
      ·
        refine ⟨16522324632861278129129663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11014883088574185419419775 16522324632861278129129663)
        ·
          refine ⟨24783486949291917193694495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16522324632861278129129663 24783486949291917193694495)
          ·
            refine ⟨37175230423937875790541743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24783486949291917193694495 37175230423937875790541743)
            ·
              refine ⟨55762845635906813685812615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37175230423937875790541743 55762845635906813685812615)
              ·
                refine ⟨83644268453860220528718923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55762845635906813685812615 83644268453860220528718923)
                ·
                  refine ⟨125466402680790330793078385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83644268453860220528718923 125466402680790330793078385)
                  ·
                    refine ⟨94099802010592748094808789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125466402680790330793078385 94099802010592748094808789)
                    ·
                      refine ⟨2205464109623267533472081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94099802010592748094808789 2205464109623267533472081)
                      ·
                        rfl

theorem cell23_4295126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4295126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295126 prefixEnd_4295126 := by exact prefixLift 4295126
  have htrace : WordTrace (prefixWord ++ tailWord_4295126) baseStart_4295126 baseEnd_4295126 := by
    simpa [prefixWord, tailWord_4295126, baseEnd_4295126] using wordTrace_append hprefix tailTrace_4295126
  have hstable : (prefixWord ++ tailWord_4295126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295126).length < 2 ^ (prefixWord ++ tailWord_4295126).sum := by decide
  have hdescent : baseEnd_4295126 < baseStart_4295126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295136 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 2, 5, 2]
def baseStart_4295136 : Nat := 118140960795 + 4295136 * 2 ^ 59
def prefixEnd_4295136 : Nat := 4983230072969 + 3 ^ 40 * 4295136 * 2
def baseEnd_4295136 : Nat := 2205469244429812494347035

theorem tailTrace_4295136 : CollatzResearch.WordTrace tailWord_4295136 prefixEnd_4295136 2205469244429812494347035 := by
  unfold tailWord_4295136
  simp only [CollatzResearch.WordTrace]
  refine ⟨78328239883731648836472631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104437653178308865115296841 78328239883731648836472631)
  ·
    refine ⟨117492359825597473254708947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78328239883731648836472631 117492359825597473254708947)
    ·
      refine ⟨176238539738396209882063421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117492359825597473254708947 176238539738396209882063421)
      ·
        refine ⟨66089452401898578705773783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176238539738396209882063421 66089452401898578705773783)
        ·
          refine ⟨99134178602847868058660675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66089452401898578705773783 99134178602847868058660675)
          ·
            refine ⟨148701267904271802087991013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99134178602847868058660675 148701267904271802087991013)
            ·
              refine ⟨27881487732050962891498315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148701267904271802087991013 27881487732050962891498315)
              ·
                refine ⟨41822231598076444337247473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27881487732050962891498315 41822231598076444337247473)
                ·
                  refine ⟨31366673698557333252935605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41822231598076444337247473 31366673698557333252935605)
                  ·
                    refine ⟨2940625659239749992462713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31366673698557333252935605 2940625659239749992462713)
                    ·
                      refine ⟨2205469244429812494347035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940625659239749992462713 2205469244429812494347035)
                      ·
                        rfl

theorem cell23_4295136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_4295136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295136 prefixEnd_4295136 := by exact prefixLift 4295136
  have htrace : WordTrace (prefixWord ++ tailWord_4295136) baseStart_4295136 baseEnd_4295136 := by
    simpa [prefixWord, tailWord_4295136, baseEnd_4295136] using wordTrace_append hprefix tailTrace_4295136
  have hstable : (prefixWord ++ tailWord_4295136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295136).length < 2 ^ (prefixWord ++ tailWord_4295136).sum := by decide
  have hdescent : baseEnd_4295136 < baseStart_4295136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295193 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 1, 4]
def baseStart_4295193 : Nat := 118140960795 + 4295193 * 2 ^ 59
def prefixEnd_4295193 : Nat := 4983230072969 + 3 ^ 40 * 4295193 * 2
def baseEnd_4295193 : Nat := 735166170942372923778091

theorem tailTrace_4295193 : CollatzResearch.WordTrace tailWord_4295193 prefixEnd_4295193 735166170942372923778091 := by
  unfold tailWord_4295193
  simp only [CollatzResearch.WordTrace]
  refine ⟨156658558728256796407770233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104439039152171197605180155 156658558728256796407770233)
  ·
    refine ⟨117493919046192597305827675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156658558728256796407770233 117493919046192597305827675)
    ·
      refine ⟨176240878569288895958741513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117493919046192597305827675 176240878569288895958741513)
      ·
        refine ⟨132180658926966671969056135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176240878569288895958741513 132180658926966671969056135)
        ·
          refine ⟨198270988390450007953584203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132180658926966671969056135 198270988390450007953584203)
          ·
            refine ⟨297406482585675011930376305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198270988390450007953584203 297406482585675011930376305)
            ·
              refine ⟨223054861939256258947782229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297406482585675011930376305 223054861939256258947782229)
              ·
                refine ⟨2613924163350659284544323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 223054861939256258947782229 2613924163350659284544323)
                ·
                  refine ⟨3920886245025988926816485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613924163350659284544323 3920886245025988926816485)
                  ·
                    refine ⟨735166170942372923778091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920886245025988926816485 735166170942372923778091)
                    ·
                      rfl

theorem cell23_4295193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 4].length) (baseStart_4295193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295193 prefixEnd_4295193 := by exact prefixLift 4295193
  have htrace : WordTrace (prefixWord ++ tailWord_4295193) baseStart_4295193 baseEnd_4295193 := by
    simpa [prefixWord, tailWord_4295193, baseEnd_4295193] using wordTrace_append hprefix tailTrace_4295193
  have hstable : (prefixWord ++ tailWord_4295193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295193).length < 2 ^ (prefixWord ++ tailWord_4295193).sum := by decide
  have hdescent : baseEnd_4295193 < baseStart_4295193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295200 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4295200 : Nat := 118140960795 + 4295200 * 2 ^ 59
def prefixEnd_4295200 : Nat := 4983230072969 + 3 ^ 40 * 4295200 * 2
def baseEnd_4295200 : Nat := 2205502107191700243946741

theorem tailTrace_4295200 : CollatzResearch.WordTrace tailWord_4295200 prefixEnd_4295200 2205502107191700243946741 := by
  unfold tailWord_4295200
  simp only [CollatzResearch.WordTrace]
  refine ⟨78329407019615718301637527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104439209359487624402183369 78329407019615718301637527)
  ·
    refine ⟨117494110529423577452456291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78329407019615718301637527 117494110529423577452456291)
    ·
      refine ⟨176241165794135366178684437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117494110529423577452456291 176241165794135366178684437)
      ·
        refine ⟨8261304646600095289625833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 176241165794135366178684437 8261304646600095289625833)
        ·
          refine ⟨6195978484950071467219375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8261304646600095289625833 6195978484950071467219375)
          ·
            refine ⟨9293967727425107200829063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195978484950071467219375 9293967727425107200829063)
            ·
              refine ⟨13940951591137660801243595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9293967727425107200829063 13940951591137660801243595)
              ·
                refine ⟨20911427386706491201865393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13940951591137660801243595 20911427386706491201865393)
                ·
                  refine ⟨15683570540029868401399045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20911427386706491201865393 15683570540029868401399045)
                  ·
                    refine ⟨2940669476255600325262321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15683570540029868401399045 2940669476255600325262321)
                    ·
                      refine ⟨2205502107191700243946741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940669476255600325262321 2205502107191700243946741)
                      ·
                        rfl

theorem cell23_4295200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4295200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295200 prefixEnd_4295200 := by exact prefixLift 4295200
  have htrace : WordTrace (prefixWord ++ tailWord_4295200) baseStart_4295200 baseEnd_4295200 := by
    simpa [prefixWord, tailWord_4295200, baseEnd_4295200] using wordTrace_append hprefix tailTrace_4295200
  have hstable : (prefixWord ++ tailWord_4295200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295200).length < 2 ^ (prefixWord ++ tailWord_4295200).sum := by decide
  have hdescent : baseEnd_4295200 < baseStart_4295200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295243 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 2, 3, 2]
def baseStart_4295243 : Nat := 118140960795 + 4295243 * 2 ^ 59
def prefixEnd_4295243 : Nat := 4983230072969 + 3 ^ 40 * 4295243 * 2
def baseEnd_4295243 : Nat := 2205524186859843575709043

theorem tailTrace_4295243 : CollatzResearch.WordTrace tailWord_4295243 prefixEnd_4295243 2205524186859843575709043 := by
  unfold tailWord_4295243
  simp only [CollatzResearch.WordTrace]
  refine ⟨156660382378075654947090383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104440254918717103298060255 156660382378075654947090383)
  ·
    refine ⟨234990573567113482420635575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156660382378075654947090383 234990573567113482420635575)
    ·
      refine ⟨352485860350670223630953363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234990573567113482420635575 352485860350670223630953363)
      ·
        refine ⟨528728790526005335446430045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352485860350670223630953363 528728790526005335446430045)
        ·
          refine ⟨198273296447252000792411267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528728790526005335446430045 198273296447252000792411267)
          ·
            refine ⟨297409944670878001188616901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198273296447252000792411267 297409944670878001188616901)
            ·
              refine ⟨55764364625789625222865669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297409944670878001188616901 55764364625789625222865669)
              ·
                refine ⟨10455818367335554729287313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55764364625789625222865669 10455818367335554729287313)
                ·
                  refine ⟨7841863775501666046965485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10455818367335554729287313 7841863775501666046965485)
                  ·
                    refine ⟨2940698915813124767612057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7841863775501666046965485 2940698915813124767612057)
                    ·
                      refine ⟨2205524186859843575709043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940698915813124767612057 2205524186859843575709043)
                      ·
                        rfl

theorem cell23_4295243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3, 2].length) (baseStart_4295243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295243 prefixEnd_4295243 := by exact prefixLift 4295243
  have htrace : WordTrace (prefixWord ++ tailWord_4295243) baseStart_4295243 baseEnd_4295243 := by
    simpa [prefixWord, tailWord_4295243, baseEnd_4295243] using wordTrace_append hprefix tailTrace_4295243
  have hstable : (prefixWord ++ tailWord_4295243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295243).length < 2 ^ (prefixWord ++ tailWord_4295243).sum := by decide
  have hdescent : baseEnd_4295243 < baseStart_4295243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295250 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_4295250 : Nat := 118140960795 + 4295250 * 2 ^ 59
def prefixEnd_4295250 : Nat := 4983230072969 + 3 ^ 40 * 4295250 * 2
def baseEnd_4295250 : Nat := 2205527781224425048321511

theorem tailTrace_4295250 : CollatzResearch.WordTrace tailWord_4295250 prefixEnd_4295250 2205527781224425048321511 := by
  unfold tailWord_4295250
  simp only [CollatzResearch.WordTrace]
  refine ⟨39165159422262573785648801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104440425126033530095063469 39165159422262573785648801)
  ·
    refine ⟨29373869566696930339236601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39165159422262573785648801 29373869566696930339236601)
    ·
      refine ⟨22030402175022697754427451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29373869566696930339236601 22030402175022697754427451)
      ·
        refine ⟨33045603262534046631641177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22030402175022697754427451 33045603262534046631641177)
        ·
          refine ⟨24784202446900534973730883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33045603262534046631641177 24784202446900534973730883)
          ·
            refine ⟨37176303670350802460596325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24784202446900534973730883 37176303670350802460596325)
            ·
              refine ⟨6970556938190775461361811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37176303670350802460596325 6970556938190775461361811)
              ·
                refine ⟨10455835407286163192042717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6970556938190775461361811 10455835407286163192042717)
                ·
                  refine ⟨3920938277732311197016019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10455835407286163192042717 3920938277732311197016019)
                  ·
                    refine ⟨5881407416598466795524029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3920938277732311197016019 5881407416598466795524029)
                    ·
                      refine ⟨2205527781224425048321511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5881407416598466795524029 2205527781224425048321511)
                      ·
                        rfl

theorem cell23_4295250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_4295250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295250 prefixEnd_4295250 := by exact prefixLift 4295250
  have htrace : WordTrace (prefixWord ++ tailWord_4295250) baseStart_4295250 baseEnd_4295250 := by
    simpa [prefixWord, tailWord_4295250, baseEnd_4295250] using wordTrace_append hprefix tailTrace_4295250
  have hstable : (prefixWord ++ tailWord_4295250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295250).length < 2 ^ (prefixWord ++ tailWord_4295250).sum := by decide
  have hdescent : baseEnd_4295250 < baseStart_4295250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295256 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_4295256 : Nat := 118140960795 + 4295256 * 2 ^ 59
def prefixEnd_4295256 : Nat := 4983230072969 + 3 ^ 40 * 4295256 * 2
def baseEnd_4295256 : Nat := 2205530862108352024846483

theorem tailTrace_4295256 : CollatzResearch.WordTrace tailWord_4295256 prefixEnd_4295256 2205530862108352024846483 := by
  unfold tailWord_4295256
  simp only [CollatzResearch.WordTrace]
  refine ⟨78330428263514279083656811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104440571018019038778209081 78330428263514279083656811)
  ·
    refine ⟨117495642395271418625485217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78330428263514279083656811 117495642395271418625485217)
    ·
      refine ⟨88121731796453563969113913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117495642395271418625485217 88121731796453563969113913)
      ·
        refine ⟨66091298847340172976835435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88121731796453563969113913 66091298847340172976835435)
        ·
          refine ⟨99136948271010259465253153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66091298847340172976835435 99136948271010259465253153)
          ·
            refine ⟨74352711203257694598939865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99136948271010259465253153 74352711203257694598939865)
            ·
              refine ⟨55764533402443270949204899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74352711203257694598939865 55764533402443270949204899)
              ·
                refine ⟨83646800103664906423807349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55764533402443270949204899 83646800103664906423807349)
                ·
                  refine ⟨7841887509718584977231939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83646800103664906423807349 7841887509718584977231939)
                  ·
                    refine ⟨11762831264577877465847909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7841887509718584977231939 11762831264577877465847909)
                    ·
                      refine ⟨2205530862108352024846483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11762831264577877465847909 2205530862108352024846483)
                      ·
                        rfl

theorem cell23_4295256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_4295256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295256 prefixEnd_4295256 := by exact prefixLift 4295256
  have htrace : WordTrace (prefixWord ++ tailWord_4295256) baseStart_4295256 baseEnd_4295256 := by
    simpa [prefixWord, tailWord_4295256, baseEnd_4295256] using wordTrace_append hprefix tailTrace_4295256
  have hstable : (prefixWord ++ tailWord_4295256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295256).length < 2 ^ (prefixWord ++ tailWord_4295256).sum := by decide
  have hdescent : baseEnd_4295256 < baseStart_4295256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295296 : List Nat := [2, 1, 1, 2, 1, 7, 9]
def baseStart_4295296 : Nat := 118140960795 + 4295296 * 2 ^ 59
def prefixEnd_4295296 : Nat := 4983230072969 + 3 ^ 40 * 4295296 * 2
def baseEnd_4295296 : Nat := 27229029646105331707979

theorem tailTrace_4295296 : CollatzResearch.WordTrace tailWord_4295296 prefixEnd_4295296 27229029646105331707979 := by
  unfold tailWord_4295296
  simp only [CollatzResearch.WordTrace]
  refine ⟨78331157723441822499384871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104441543631255763332513161 78331157723441822499384871)
  ·
    refine ⟨117496736585162733749077307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78331157723441822499384871 117496736585162733749077307)
    ·
      refine ⟨176245104877744100623615961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117496736585162733749077307 176245104877744100623615961)
      ·
        refine ⟨132183828658308075467711971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176245104877744100623615961 132183828658308075467711971)
        ·
          refine ⟨198275742987462113201567957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132183828658308075467711971 198275742987462113201567957)
          ·
            refine ⟨4647087726268643278161749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 198275742987462113201567957 4647087726268643278161749)
            ·
              refine ⟨27229029646105331707979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4647087726268643278161749 27229029646105331707979)
              ·
                rfl

theorem cell23_4295296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 9].length) (baseStart_4295296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295296 prefixEnd_4295296 := by exact prefixLift 4295296
  have htrace : WordTrace (prefixWord ++ tailWord_4295296) baseStart_4295296 baseEnd_4295296 := by
    simpa [prefixWord, tailWord_4295296, baseEnd_4295296] using wordTrace_append hprefix tailTrace_4295296
  have hstable : (prefixWord ++ tailWord_4295296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295296).length < 2 ^ (prefixWord ++ tailWord_4295296).sum := by decide
  have hdescent : baseEnd_4295296 < baseStart_4295296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295357 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_4295357 : Nat := 118140960795 + 4295357 * 2 ^ 59
def prefixEnd_4295357 : Nat := 4983230072969 + 3 ^ 40 * 4295357 * 2
def baseEnd_4295357 : Nat := 2205582723654456129683519

theorem tailTrace_4295357 : CollatzResearch.WordTrace tailWord_4295357 prefixEnd_4295357 2205582723654456129683519 := by
  unfold tailWord_4295357
  simp only [CollatzResearch.WordTrace]
  refine ⟨156664540299662652416740325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104443026866441768277826883 156664540299662652416740325)
  ·
    refine ⟨29374601306186747328138811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156664540299662652416740325 29374601306186747328138811)
    ·
      refine ⟨44061901959280120992208217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29374601306186747328138811 44061901959280120992208217)
      ·
        refine ⟨33046426469460090744156163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44061901959280120992208217 33046426469460090744156163)
        ·
          refine ⟨49569639704190136116234245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33046426469460090744156163 49569639704190136116234245)
          ·
            refine ⟨9294307444535650521793921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49569639704190136116234245 9294307444535650521793921)
            ·
              refine ⟨6970730583401737891345441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9294307444535650521793921 6970730583401737891345441)
              ·
                refine ⟨5228047937551303418509081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6970730583401737891345441 5228047937551303418509081)
                ·
                  refine ⟨3921035953163477563881811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5228047937551303418509081 3921035953163477563881811)
                  ·
                    refine ⟨5881553929745216345822717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3921035953163477563881811 5881553929745216345822717)
                    ·
                      refine ⟨2205582723654456129683519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5881553929745216345822717 2205582723654456129683519)
                      ·
                        rfl

theorem cell23_4295357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_4295357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295357 prefixEnd_4295357 := by exact prefixLift 4295357
  have htrace : WordTrace (prefixWord ++ tailWord_4295357) baseStart_4295357 baseEnd_4295357 := by
    simpa [prefixWord, tailWord_4295357, baseEnd_4295357] using wordTrace_append hprefix tailTrace_4295357
  have hstable : (prefixWord ++ tailWord_4295357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295357).length < 2 ^ (prefixWord ++ tailWord_4295357).sum := by decide
  have hdescent : baseEnd_4295357 < baseStart_4295357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295420 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 5]
def baseStart_4295420 : Nat := 118140960795 + 4295420 * 2 ^ 59
def prefixEnd_4295420 : Nat := 4983230072969 + 3 ^ 40 * 4295420 * 2
def baseEnd_4295420 : Nat := 245068341437298820355081

theorem tailTrace_4295420 : CollatzResearch.WordTrace tailWord_4295420 prefixEnd_4295420 245068341437298820355081 := by
  unfold tailWord_4295420
  simp only [CollatzResearch.WordTrace]
  refine ⟨78333419049217207088141857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104444558732289609450855809 78333419049217207088141857)
  ·
    refine ⟨58750064286912905316106393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78333419049217207088141857 58750064286912905316106393)
    ·
      refine ⟨44062548215184678987079795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58750064286912905316106393 44062548215184678987079795)
      ·
        refine ⟨66093822322777018480619693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44062548215184678987079795 66093822322777018480619693)
        ·
          refine ⟨24785183371041381930232385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66093822322777018480619693 24785183371041381930232385)
          ·
            refine ⟨18588887528281036447674289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24785183371041381930232385 18588887528281036447674289)
            ·
              refine ⟨13941665646210777335755717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18588887528281036447674289 13941665646210777335755717)
              ·
                refine ⟨2614062308664520750454197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13941665646210777335755717 2614062308664520750454197)
                ·
                  refine ⟨245068341437298820355081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2614062308664520750454197 245068341437298820355081)
                  ·
                    rfl

theorem cell23_4295420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_4295420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295420 prefixEnd_4295420 := by exact prefixLift 4295420
  have htrace : WordTrace (prefixWord ++ tailWord_4295420) baseStart_4295420 baseEnd_4295420 := by
    simpa [prefixWord, tailWord_4295420, baseEnd_4295420] using wordTrace_append hprefix tailTrace_4295420
  have hstable : (prefixWord ++ tailWord_4295420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295420).length < 2 ^ (prefixWord ++ tailWord_4295420).sum := by decide
  have hdescent : baseEnd_4295420 < baseStart_4295420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295431 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4295431 : Nat := 118140960795 + 4295431 * 2 ^ 59
def prefixEnd_4295431 : Nat := 4983230072969 + 3 ^ 40 * 4295431 * 2
def baseEnd_4295431 : Nat := 2205620721222888840158179

theorem tailTrace_4295431 : CollatzResearch.WordTrace tailWord_4295431 prefixEnd_4295431 2205620721222888840158179 := by
  unfold tailWord_4295431
  simp only [CollatzResearch.WordTrace]
  refine ⟨156667239301394563054934147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104444826200929708703289431 156667239301394563054934147)
  ·
    refine ⟨235000858952091844582401221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156667239301394563054934147 235000858952091844582401221)
    ·
      refine ⟨44062661053517220859200229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235000858952091844582401221 44062661053517220859200229)
      ·
        refine ⟨8261748947534478911100043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44062661053517220859200229 8261748947534478911100043)
        ·
          refine ⟨12392623421301718366650065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8261748947534478911100043 12392623421301718366650065)
          ·
            refine ⟨9294467565976288774987549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12392623421301718366650065 9294467565976288774987549)
            ·
              refine ⟨3485425337241108290620331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9294467565976288774987549 3485425337241108290620331)
              ·
                refine ⟨5228138005861662435930497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3485425337241108290620331 5228138005861662435930497)
                ·
                  refine ⟨3921103504396246826947873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5228138005861662435930497 3921103504396246826947873)
                  ·
                    refine ⟨2940827628297185120210905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921103504396246826947873 2940827628297185120210905)
                    ·
                      refine ⟨2205620721222888840158179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940827628297185120210905 2205620721222888840158179)
                      ·
                        rfl

theorem cell23_4295431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4295431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295431 prefixEnd_4295431 := by exact prefixLift 4295431
  have htrace : WordTrace (prefixWord ++ tailWord_4295431) baseStart_4295431 baseEnd_4295431 := by
    simpa [prefixWord, tailWord_4295431, baseEnd_4295431] using wordTrace_append hprefix tailTrace_4295431
  have hstable : (prefixWord ++ tailWord_4295431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295431).length < 2 ^ (prefixWord ++ tailWord_4295431).sum := by decide
  have hdescent : baseEnd_4295431 < baseStart_4295431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295577 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 7, 2, 2]
def baseStart_4295577 : Nat := 118140960795 + 4295577 * 2 ^ 59
def prefixEnd_4295577 : Nat := 4983230072969 + 3 ^ 40 * 4295577 * 2
def baseEnd_4295577 : Nat := 2205695689398445268932507

theorem tailTrace_4295577 : CollatzResearch.WordTrace tailWord_4295577 prefixEnd_4295577 2205695689398445268932507 := by
  unfold tailWord_4295577
  simp only [CollatzResearch.WordTrace]
  refine ⟨156672564358865629989748985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104448376239243753326499323 156672564358865629989748985)
  ·
    refine ⟨117504423269149222492311739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156672564358865629989748985 117504423269149222492311739)
    ·
      refine ⟨176256634903723833738467609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117504423269149222492311739 176256634903723833738467609)
      ·
        refine ⟨132192476177792875303850707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176256634903723833738467609 132192476177792875303850707)
        ·
          refine ⟨198288714266689312955776061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132192476177792875303850707 198288714266689312955776061)
          ·
            refine ⟨74358267850008492358416023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198288714266689312955776061 74358267850008492358416023)
            ·
              refine ⟨111537401775012738537624035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74358267850008492358416023 111537401775012738537624035)
              ·
                refine ⟨167306102662519107806436053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111537401775012738537624035 167306102662519107806436053)
                ·
                  refine ⟨3921236781152791589213345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 167306102662519107806436053 3921236781152791589213345)
                  ·
                    refine ⟨2940927585864593691910009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921236781152791589213345 2940927585864593691910009)
                    ·
                      refine ⟨2205695689398445268932507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940927585864593691910009 2205695689398445268932507)
                      ·
                        rfl

theorem cell23_4295577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_4295577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295577 prefixEnd_4295577 := by exact prefixLift 4295577
  have htrace : WordTrace (prefixWord ++ tailWord_4295577) baseStart_4295577 baseEnd_4295577 := by
    simpa [prefixWord, tailWord_4295577, baseEnd_4295577] using wordTrace_append hprefix tailTrace_4295577
  have hstable : (prefixWord ++ tailWord_4295577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295577).length < 2 ^ (prefixWord ++ tailWord_4295577).sum := by decide
  have hdescent : baseEnd_4295577 < baseStart_4295577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295587 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 2, 4]
def baseStart_4295587 : Nat := 118140960795 + 4295587 * 2 ^ 59
def prefixEnd_4295587 : Nat := 4983230072969 + 3 ^ 40 * 4295587 * 2
def baseEnd_4295587 : Nat := 735233608068330076602487

theorem tailTrace_4295587 : CollatzResearch.WordTrace tailWord_4295587 prefixEnd_4295587 735233608068330076602487 := by
  unfold tailWord_4295587
  simp only [CollatzResearch.WordTrace]
  refine ⟨156672929088829401697613015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104448619392552934465075343 156672929088829401697613015)
  ·
    refine ⟨235009393633244102546419523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156672929088829401697613015 235009393633244102546419523)
    ·
      refine ⟨352514090449866153819629285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235009393633244102546419523 352514090449866153819629285)
      ·
        refine ⟨66096391959349903841180491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 352514090449866153819629285 66096391959349903841180491)
        ·
          refine ⟨99144587939024855761770737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66096391959349903841180491 99144587939024855761770737)
          ·
            refine ⟨74358440954268641821328053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99144587939024855761770737 74358440954268641821328053)
            ·
              refine ⟨6971103839462685170749505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74358440954268641821328053 6971103839462685170749505)
              ·
                refine ⟨5228327879597013878062129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6971103839462685170749505 5228327879597013878062129)
                ·
                  refine ⟨3921245909697760408546597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5228327879597013878062129 3921245909697760408546597)
                  ·
                    refine ⟨735233608068330076602487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921245909697760408546597 735233608068330076602487)
                    ·
                      rfl

theorem cell23_4295587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 4].length) (baseStart_4295587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295587 prefixEnd_4295587 := by exact prefixLift 4295587
  have htrace : WordTrace (prefixWord ++ tailWord_4295587) baseStart_4295587 baseEnd_4295587 := by
    simpa [prefixWord, tailWord_4295587, baseEnd_4295587] using wordTrace_append hprefix tailTrace_4295587
  have hstable : (prefixWord ++ tailWord_4295587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295587).length < 2 ^ (prefixWord ++ tailWord_4295587).sum := by decide
  have hdescent : baseEnd_4295587 < baseStart_4295587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295603 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_4295603 : Nat := 118140960795 + 4295603 * 2 ^ 59
def prefixEnd_4295603 : Nat := 4983230072969 + 3 ^ 40 * 4295603 * 2
def baseEnd_4295603 : Nat := 2205709039895462167207387

theorem tailTrace_4295603 : CollatzResearch.WordTrace tailWord_4295603 prefixEnd_4295603 2205709039895462167207387 := by
  unfold tailWord_4295603
  simp only [CollatzResearch.WordTrace]
  refine ⟨156673512656771436430195463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104449008437847624286796975 156673512656771436430195463)
  ·
    refine ⟨235010268985157154645293195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156673512656771436430195463 235010268985157154645293195)
    ·
      refine ⟨352515403477735731967939793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235010268985157154645293195 352515403477735731967939793)
      ·
        refine ⟨264386552608301798975954845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352515403477735731967939793 264386552608301798975954845)
        ·
          refine ⟨99144957228113174615983067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264386552608301798975954845 99144957228113174615983067)
          ·
            refine ⟨148717435842169761923974601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99144957228113174615983067 148717435842169761923974601)
            ·
              refine ⟨111538076881627321442980951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148717435842169761923974601 111538076881627321442980951)
              ·
                refine ⟨167307115322440982164471427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111538076881627321442980951 167307115322440982164471427)
                ·
                  refine ⟨250960672983661473246707141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167307115322440982164471427 250960672983661473246707141)
                  ·
                    refine ⟨47055126184436526233757589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250960672983661473246707141 47055126184436526233757589)
                    ·
                      refine ⟨2205709039895462167207387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47055126184436526233757589 2205709039895462167207387)
                      ·
                        rfl

theorem cell23_4295603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_4295603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295603 prefixEnd_4295603 := by exact prefixLift 4295603
  have htrace : WordTrace (prefixWord ++ tailWord_4295603) baseStart_4295603 baseEnd_4295603 := by
    simpa [prefixWord, tailWord_4295603, baseEnd_4295603] using wordTrace_append hprefix tailTrace_4295603
  have hstable : (prefixWord ++ tailWord_4295603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295603).length < 2 ^ (prefixWord ++ tailWord_4295603).sum := by decide
  have hdescent : baseEnd_4295603 < baseStart_4295603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295604 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4295604 : Nat := 118140960795 + 4295604 * 2 ^ 59
def prefixEnd_4295604 : Nat := 4983230072969 + 3 ^ 40 * 4295604 * 2
def baseEnd_4295604 : Nat := 735236517792038887764961

theorem tailTrace_4295604 : CollatzResearch.WordTrace tailWord_4295604 prefixEnd_4295604 735236517792038887764961 := by
  unfold tailWord_4295604
  simp only [CollatzResearch.WordTrace]
  refine ⟨78336774564883906800490933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104449032753178542400654577 78336774564883906800490933)
  ·
    refine ⟨7344072615457866262546025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78336774564883906800490933 7344072615457866262546025)
    ·
      refine ⟨5508054461593399696909519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7344072615457866262546025 5508054461593399696909519)
      ·
        refine ⟨8262081692390099545364279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5508054461593399696909519 8262081692390099545364279)
        ·
          refine ⟨12393122538585149318046419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8262081692390099545364279 12393122538585149318046419)
          ·
            refine ⟨18589683807877723977069629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12393122538585149318046419 18589683807877723977069629)
            ·
              refine ⟨6971131427954146491401111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18589683807877723977069629 6971131427954146491401111)
              ·
                refine ⟨10456697141931219737101667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6971131427954146491401111 10456697141931219737101667)
                ·
                  refine ⟨15685045712896829605652501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10456697141931219737101667 15685045712896829605652501)
                  ·
                    refine ⟨735236517792038887764961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15685045712896829605652501 735236517792038887764961)
                    ·
                      rfl

theorem cell23_4295604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4295604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295604 prefixEnd_4295604 := by exact prefixLift 4295604
  have htrace : WordTrace (prefixWord ++ tailWord_4295604) baseStart_4295604 baseEnd_4295604 := by
    simpa [prefixWord, tailWord_4295604, baseEnd_4295604] using wordTrace_append hprefix tailTrace_4295604
  have hstable : (prefixWord ++ tailWord_4295604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295604).length < 2 ^ (prefixWord ++ tailWord_4295604).sum := by decide
  have hdescent : baseEnd_4295604 < baseStart_4295604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295614 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_4295614 : Nat := 118140960795 + 4295614 * 2 ^ 59
def prefixEnd_4295614 : Nat := 4983230072969 + 3 ^ 40 * 4295614 * 2
def baseEnd_4295614 : Nat := 2205714688182661624169837

theorem tailTrace_4295614 : CollatzResearch.WordTrace tailWord_4295614 prefixEnd_4295614 2205714688182661624169837 := by
  unfold tailWord_4295614
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584239232466448163605737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104449275906487723539230597 19584239232466448163605737)
  ·
    refine ⟨14688179424349836122704303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19584239232466448163605737 14688179424349836122704303)
    ·
      refine ⟨22032269136524754184056455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14688179424349836122704303 22032269136524754184056455)
      ·
        refine ⟨33048403704787131276084683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22032269136524754184056455 33048403704787131276084683)
        ·
          refine ⟨49572605557180696914127025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33048403704787131276084683 49572605557180696914127025)
          ·
            refine ⟨37179454167885522685595269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49572605557180696914127025 37179454167885522685595269)
            ·
              refine ⟨6971147656478535503549113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37179454167885522685595269 6971147656478535503549113)
              ·
                refine ⟨5228360742358901627661835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6971147656478535503549113 5228360742358901627661835)
                ·
                  refine ⟨7842541113538352441492753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5228360742358901627661835 7842541113538352441492753)
                  ·
                    refine ⟨5881905835153764331119565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7842541113538352441492753 5881905835153764331119565)
                    ·
                      refine ⟨2205714688182661624169837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5881905835153764331119565 2205714688182661624169837)
                      ·
                        rfl

theorem cell23_4295614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_4295614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295614 prefixEnd_4295614 := by exact prefixLift 4295614
  have htrace : WordTrace (prefixWord ++ tailWord_4295614) baseStart_4295614 baseEnd_4295614 := by
    simpa [prefixWord, tailWord_4295614, baseEnd_4295614] using wordTrace_append hprefix tailTrace_4295614
  have hstable : (prefixWord ++ tailWord_4295614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295614).length < 2 ^ (prefixWord ++ tailWord_4295614).sum := by decide
  have hdescent : baseEnd_4295614 < baseStart_4295614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295627 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 3]
def baseStart_4295627 : Nat := 118140960795 + 4295627 * 2 ^ 59
def prefixEnd_4295627 : Nat := 4983230072969 + 3 ^ 40 * 4295627 * 2
def baseEnd_4295627 : Nat := 2205721363431170073307277

theorem tailTrace_4295627 : CollatzResearch.WordTrace tailWord_4295627 prefixEnd_4295627 2205721363431170073307277 := by
  unfold tailWord_4295627
  simp only [CollatzResearch.WordTrace]
  refine ⟨156674388008684488529069135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104449592005789659019379423 156674388008684488529069135)
  ·
    refine ⟨235011582013026732793603703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156674388008684488529069135 235011582013026732793603703)
    ·
      refine ⟨352517373019540099190405555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235011582013026732793603703 352517373019540099190405555)
      ·
        refine ⟨528776059529310148785608333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352517373019540099190405555 528776059529310148785608333)
        ·
          refine ⟨198291022323491305794603125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528776059529310148785608333 198291022323491305794603125)
          ·
            refine ⟨18589783342827309918244043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198291022323491305794603125 18589783342827309918244043)
            ·
              refine ⟨27884675014240964877366065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18589783342827309918244043 27884675014240964877366065)
              ·
                refine ⟨20913506260680723658024549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27884675014240964877366065 20913506260680723658024549)
                ·
                  refine ⟨3921282423877635685879603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20913506260680723658024549 3921282423877635685879603)
                  ·
                    refine ⟨5881923635816453528819405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3921282423877635685879603 5881923635816453528819405)
                    ·
                      refine ⟨2205721363431170073307277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5881923635816453528819405 2205721363431170073307277)
                      ·
                        rfl

theorem cell23_4295627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 3].length) (baseStart_4295627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295627 prefixEnd_4295627 := by exact prefixLift 4295627
  have htrace : WordTrace (prefixWord ++ tailWord_4295627) baseStart_4295627 baseEnd_4295627 := by
    simpa [prefixWord, tailWord_4295627, baseEnd_4295627] using wordTrace_append hprefix tailTrace_4295627
  have hstable : (prefixWord ++ tailWord_4295627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295627).length < 2 ^ (prefixWord ++ tailWord_4295627).sum := by decide
  have hdescent : baseEnd_4295627 < baseStart_4295627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295645 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_4295645 : Nat := 118140960795 + 4295645 * 2 ^ 59
def prefixEnd_4295645 : Nat := 4983230072969 + 3 ^ 40 * 4295645 * 2
def baseEnd_4295645 : Nat := 2205730606082951002882195

theorem tailTrace_4295645 : CollatzResearch.WordTrace tailWord_4295645 prefixEnd_4295645 2205730606082951002882195 := by
  unfold tailWord_4295645
  simp only [CollatzResearch.WordTrace]
  refine ⟨156675044522619277603224389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104450029681746185068816259 156675044522619277603224389)
  ·
    refine ⟨29376570847991114550604573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156675044522619277603224389 29376570847991114550604573)
    ·
      refine ⟨11016214067996667956476715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29376570847991114550604573 11016214067996667956476715)
      ·
        refine ⟨16524321101995001934715073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11016214067996667956476715 16524321101995001934715073)
        ·
          refine ⟨12393240826496251451036305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16524321101995001934715073 12393240826496251451036305)
          ·
            refine ⟨9294930619872188588277229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12393240826496251451036305 9294930619872188588277229)
            ·
              refine ⟨3485598982452070720603961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9294930619872188588277229 3485598982452070720603961)
              ·
                refine ⟨2614199236839053040452971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485598982452070720603961 2614199236839053040452971)
                ·
                  refine ⟨3921298855258579560679457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614199236839053040452971 3921298855258579560679457)
                  ·
                    refine ⟨2940974141443934670509593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921298855258579560679457 2940974141443934670509593)
                    ·
                      refine ⟨2205730606082951002882195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940974141443934670509593 2205730606082951002882195)
                      ·
                        rfl

theorem cell23_4295645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_4295645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295645 prefixEnd_4295645 := by exact prefixLift 4295645
  have htrace : WordTrace (prefixWord ++ tailWord_4295645) baseStart_4295645 baseEnd_4295645 := by
    simpa [prefixWord, tailWord_4295645, baseEnd_4295645] using wordTrace_append hprefix tailTrace_4295645
  have hstable : (prefixWord ++ tailWord_4295645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295645).length < 2 ^ (prefixWord ++ tailWord_4295645).sum := by decide
  have hdescent : baseEnd_4295645 < baseStart_4295645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295701 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_4295701 : Nat := 118140960795 + 4295701 * 2 ^ 59
def prefixEnd_4295701 : Nat := 4983230072969 + 3 ^ 40 * 4295701 * 2
def baseEnd_4295701 : Nat := 2205759360999602783781937

theorem tailTrace_4295701 : CollatzResearch.WordTrace tailWord_4295701 prefixEnd_4295701 2205759360999602783781937 := by
  unfold tailWord_4295701
  simp only [CollatzResearch.WordTrace]
  refine ⟨156677087010416399167262957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104451391340277599444841971 156677087010416399167262957)
  ·
    refine ⟨58753907628906149687723609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156677087010416399167262957 58753907628906149687723609)
    ·
      refine ⟨44065430721679612265792707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58753907628906149687723609 44065430721679612265792707)
      ·
        refine ⟨66098146082519418398689061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44065430721679612265792707 66098146082519418398689061)
        ·
          refine ⟨12393402390472390949754199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66098146082519418398689061 12393402390472390949754199)
          ·
            refine ⟨18590103585708586424631299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12393402390472390949754199 18590103585708586424631299)
            ·
              refine ⟨27885155378562879636946949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18590103585708586424631299 27885155378562879636946949)
              ·
                refine ⟨5228466633480539931927553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27885155378562879636946949 5228466633480539931927553)
                ·
                  refine ⟨3921349975110404948945665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5228466633480539931927553 3921349975110404948945665)
                  ·
                    refine ⟨2941012481332803711709249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921349975110404948945665 2941012481332803711709249)
                    ·
                      refine ⟨2205759360999602783781937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941012481332803711709249 2205759360999602783781937)
                      ·
                        rfl

theorem cell23_4295701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_4295701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295701 prefixEnd_4295701 := by exact prefixLift 4295701
  have htrace : WordTrace (prefixWord ++ tailWord_4295701) baseStart_4295701 baseEnd_4295701 := by
    simpa [prefixWord, tailWord_4295701, baseEnd_4295701] using wordTrace_append hprefix tailTrace_4295701
  have hstable : (prefixWord ++ tailWord_4295701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295701).length < 2 ^ (prefixWord ++ tailWord_4295701).sum := by decide
  have hdescent : baseEnd_4295701 < baseStart_4295701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295717 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_4295717 : Nat := 118140960795 + 4295717 * 2 ^ 59
def prefixEnd_4295717 : Nat := 4983230072969 + 3 ^ 40 * 4295717 * 2
def baseEnd_4295717 : Nat := 2205767576690074721181863

theorem tailTrace_4295717 : CollatzResearch.WordTrace tailWord_4295717 prefixEnd_4295717 2205767576690074721181863 := by
  unfold tailWord_4295717
  simp only [CollatzResearch.WordTrace]
  refine ⟨156677670578358433899845405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104451780385572289266563603 156677670578358433899845405)
  ·
    refine ⟨58754126466884412712442027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156677670578358433899845405 58754126466884412712442027)
    ·
      refine ⟨88131189700326619068663041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58754126466884412712442027 88131189700326619068663041)
      ·
        refine ⟨66098392275244964301497281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88131189700326619068663041 66098392275244964301497281)
        ·
          refine ⟨49573794206433723226122961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66098392275244964301497281 49573794206433723226122961)
          ·
            refine ⟨37180345654825292419592221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49573794206433723226122961 37180345654825292419592221)
            ·
              refine ⟨13942629620559484657347083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37180345654825292419592221 13942629620559484657347083)
              ·
                refine ⟨20913944430839226986020625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13942629620559484657347083 20913944430839226986020625)
                ·
                  refine ⟨15685458323129420239515469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20913944430839226986020625 15685458323129420239515469)
                  ·
                    refine ⟨5882046871173532589818301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15685458323129420239515469 5882046871173532589818301)
                    ·
                      refine ⟨2205767576690074721181863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5882046871173532589818301 2205767576690074721181863)
                      ·
                        rfl

theorem cell23_4295717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_4295717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295717 prefixEnd_4295717 := by exact prefixLift 4295717
  have htrace : WordTrace (prefixWord ++ tailWord_4295717) baseStart_4295717 baseEnd_4295717 := by
    simpa [prefixWord, tailWord_4295717, baseEnd_4295717] using wordTrace_append hprefix tailTrace_4295717
  have hstable : (prefixWord ++ tailWord_4295717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295717).length < 2 ^ (prefixWord ++ tailWord_4295717).sum := by decide
  have hdescent : baseEnd_4295717 < baseStart_4295717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295737 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_4295737 : Nat := 118140960795 + 4295737 * 2 ^ 59
def prefixEnd_4295737 : Nat := 4983230072969 + 3 ^ 40 * 4295737 * 2
def baseEnd_4295737 : Nat := 735259282101054880977257

theorem tailTrace_4295737 : CollatzResearch.WordTrace tailWord_4295737 prefixEnd_4295737 735259282101054880977257 := by
  unfold tailWord_4295737
  simp only [CollatzResearch.WordTrace]
  refine ⟨156678400038285977315573465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104452266692190651543715643 156678400038285977315573465)
  ·
    refine ⟨117508800028714482986680099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156678400038285977315573465 117508800028714482986680099)
    ·
      refine ⟨176263200043071724480020149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117508800028714482986680099 176263200043071724480020149)
      ·
        refine ⟨16524675004037974170001889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176263200043071724480020149 16524675004037974170001889)
        ·
          refine ⟨12393506253028480627501417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16524675004037974170001889 12393506253028480627501417)
          ·
            refine ⟨9295129689771360470626063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12393506253028480627501417 9295129689771360470626063)
            ·
              refine ⟨13942694534657040705939095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9295129689771360470626063 13942694534657040705939095)
              ·
                refine ⟨20914041801985561058908643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13942694534657040705939095 20914041801985561058908643)
                ·
                  refine ⟨31371062702978341588362965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20914041801985561058908643 31371062702978341588362965)
                  ·
                    refine ⟨735259282101054880977257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31371062702978341588362965 735259282101054880977257)
                    ·
                      rfl

theorem cell23_4295737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_4295737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295737 prefixEnd_4295737 := by exact prefixLift 4295737
  have htrace : WordTrace (prefixWord ++ tailWord_4295737) baseStart_4295737 baseEnd_4295737 := by
    simpa [prefixWord, tailWord_4295737, baseEnd_4295737] using wordTrace_append hprefix tailTrace_4295737
  have hstable : (prefixWord ++ tailWord_4295737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295737).length < 2 ^ (prefixWord ++ tailWord_4295737).sum := by decide
  have hdescent : baseEnd_4295737 < baseStart_4295737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295760 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_4295760 : Nat := 118140960795 + 4295760 * 2 ^ 59
def prefixEnd_4295760 : Nat := 4983230072969 + 3 ^ 40 * 4295760 * 2
def baseEnd_4295760 : Nat := 2205789656358218052944165

theorem tailTrace_4295760 : CollatzResearch.WordTrace tailWord_4295760 prefixEnd_4295760 2205789656358218052944165 := by
  unfold tailWord_4295760
  simp only [CollatzResearch.WordTrace]
  refine ⟨78339619458601326121830367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104452825944801768162440489 78339619458601326121830367)
  ·
    refine ⟨117509429187901989182745551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78339619458601326121830367 117509429187901989182745551)
    ·
      refine ⟨176264143781852983774118327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117509429187901989182745551 176264143781852983774118327)
      ·
        refine ⟨264396215672779475661177491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176264143781852983774118327 264396215672779475661177491)
        ·
          refine ⟨396594323509169213491766237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264396215672779475661177491 396594323509169213491766237)
          ·
            refine ⟨148722871315938455059412339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396594323509169213491766237 148722871315938455059412339)
            ·
              refine ⟨223084306973907682589118509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148722871315938455059412339 223084306973907682589118509)
              ·
                refine ⟨83656615115215380970919441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223084306973907682589118509 83656615115215380970919441)
                ·
                  refine ⟨62742461336411535728189581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83656615115215380970919441 62742461336411535728189581)
                  ·
                    refine ⟨23528423001154325898071093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62742461336411535728189581 23528423001154325898071093)
                    ·
                      refine ⟨2205789656358218052944165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23528423001154325898071093 2205789656358218052944165)
                      ·
                        rfl

theorem cell23_4295760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_4295760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295760 prefixEnd_4295760 := by exact prefixLift 4295760
  have htrace : WordTrace (prefixWord ++ tailWord_4295760) baseStart_4295760 baseEnd_4295760 := by
    simpa [prefixWord, tailWord_4295760, baseEnd_4295760] using wordTrace_append hprefix tailTrace_4295760
  have hstable : (prefixWord ++ tailWord_4295760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295760).length < 2 ^ (prefixWord ++ tailWord_4295760).sum := by decide
  have hdescent : baseEnd_4295760 < baseStart_4295760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295777 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_4295777 : Nat := 118140960795 + 4295777 * 2 ^ 59
def prefixEnd_4295777 : Nat := 4983230072969 + 3 ^ 40 * 4295777 * 2
def baseEnd_4295777 : Nat := 2205798385529344486431587

theorem tailTrace_4295777 : CollatzResearch.WordTrace tailWord_4295777 prefixEnd_4295777 2205798385529344486431587 := by
  unfold tailWord_4295777
  simp only [CollatzResearch.WordTrace]
  refine ⟨156679858958141064147029585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104453239305427376098019723 156679858958141064147029585)
  ·
    refine ⟨117509894218605798110272189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156679858958141064147029585 117509894218605798110272189)
    ·
      refine ⟨44066210331977174291352071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117509894218605798110272189 44066210331977174291352071)
      ·
        refine ⟨66099315497965761437028107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44066210331977174291352071 66099315497965761437028107)
        ·
          refine ⟨99148973246948642155542161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66099315497965761437028107 99148973246948642155542161)
          ·
            refine ⟨74361729935211481616656621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99148973246948642155542161 74361729935211481616656621)
            ·
              refine ⟨27885648725704305606246233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74361729935211481616656621 27885648725704305606246233)
              ·
                refine ⟨20914236544278229204684675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27885648725704305606246233 20914236544278229204684675)
                ·
                  refine ⟨31371354816417343807027013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20914236544278229204684675 31371354816417343807027013)
                  ·
                    refine ⟨5882129028078251963817565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31371354816417343807027013 5882129028078251963817565)
                    ·
                      refine ⟨2205798385529344486431587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5882129028078251963817565 2205798385529344486431587)
                      ·
                        rfl

theorem cell23_4295777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_4295777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295777 prefixEnd_4295777 := by exact prefixLift 4295777
  have htrace : WordTrace (prefixWord ++ tailWord_4295777) baseStart_4295777 baseEnd_4295777 := by
    simpa [prefixWord, tailWord_4295777, baseEnd_4295777] using wordTrace_append hprefix tailTrace_4295777
  have hstable : (prefixWord ++ tailWord_4295777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295777).length < 2 ^ (prefixWord ++ tailWord_4295777).sum := by decide
  have hdescent : baseEnd_4295777 < baseStart_4295777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295794 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4295794 : Nat := 118140960795 + 4295794 * 2 ^ 59
def prefixEnd_4295794 : Nat := 4983230072969 + 3 ^ 40 * 4295794 * 2
def baseEnd_4295794 : Nat := 2205807114700470919919009

theorem tailTrace_4295794 : CollatzResearch.WordTrace tailWord_4295794 prefixEnd_4295794 2205807114700470919919009 := by
  unfold tailWord_4295794
  simp only [CollatzResearch.WordTrace]
  refine ⟨39170119749769869012599609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104453652666052984033598957 39170119749769869012599609)
  ·
    refine ⟨29377589812327401759449707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39170119749769869012599609 29377589812327401759449707)
    ·
      refine ⟨44066384718491102639174561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29377589812327401759449707 44066384718491102639174561)
      ·
        refine ⟨33049788538868326979380921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44066384718491102639174561 33049788538868326979380921)
        ·
          refine ⟨24787341404151245234535691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33049788538868326979380921 24787341404151245234535691)
          ·
            refine ⟨37181012106226867851803537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24787341404151245234535691 37181012106226867851803537)
            ·
              refine ⟨27885759079670150888852653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37181012106226867851803537 27885759079670150888852653)
              ·
                refine ⟨10457159654876306583319745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27885759079670150888852653 10457159654876306583319745)
                ·
                  refine ⟨7842869741157229937489809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10457159654876306583319745 7842869741157229937489809)
                  ·
                    refine ⟨5882152305867922453117357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7842869741157229937489809 5882152305867922453117357)
                    ·
                      refine ⟨2205807114700470919919009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5882152305867922453117357 2205807114700470919919009)
                      ·
                        rfl

theorem cell23_4295794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4295794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295794 prefixEnd_4295794 := by exact prefixLift 4295794
  have htrace : WordTrace (prefixWord ++ tailWord_4295794) baseStart_4295794 baseEnd_4295794 := by
    simpa [prefixWord, tailWord_4295794, baseEnd_4295794] using wordTrace_append hprefix tailTrace_4295794
  have hstable : (prefixWord ++ tailWord_4295794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295794).length < 2 ^ (prefixWord ++ tailWord_4295794).sum := by decide
  have hdescent : baseEnd_4295794 < baseStart_4295794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295818 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_4295818 : Nat := 118140960795 + 4295818 * 2 ^ 59
def prefixEnd_4295818 : Nat := 4983230072969 + 3 ^ 40 * 4295818 * 2
def baseEnd_4295818 : Nat := 735273146078726275339633

theorem tailTrace_4295818 : CollatzResearch.WordTrace tailWord_4295818 prefixEnd_4295818 735273146078726275339633 := by
  unfold tailWord_4295818
  simp only [CollatzResearch.WordTrace]
  refine ⟨39170338587748132037318027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104454236233995018766181405 39170338587748132037318027)
  ·
    refine ⟨58755507881622198055977041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39170338587748132037318027 58755507881622198055977041)
    ·
      refine ⟨44066630911216648541982781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58755507881622198055977041 44066630911216648541982781)
      ·
        refine ⟨16524986591706243203243543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44066630911216648541982781 16524986591706243203243543)
        ·
          refine ⟨24787479887559364804865315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16524986591706243203243543 24787479887559364804865315)
          ·
            refine ⟨37181219831339047207297973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24787479887559364804865315 37181219831339047207297973)
            ·
              refine ⟨3485739359188035675684185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37181219831339047207297973 3485739359188035675684185)
              ·
                refine ⟨2614304519391026756763139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485739359188035675684185 2614304519391026756763139)
                ·
                  refine ⟨3921456779086540135144709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614304519391026756763139 3921456779086540135144709)
                  ·
                    refine ⟨735273146078726275339633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921456779086540135144709 735273146078726275339633)
                    ·
                      rfl

theorem cell23_4295818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_4295818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295818 prefixEnd_4295818 := by exact prefixLift 4295818
  have htrace : WordTrace (prefixWord ++ tailWord_4295818) baseStart_4295818 baseEnd_4295818 := by
    simpa [prefixWord, tailWord_4295818, baseEnd_4295818] using wordTrace_append hprefix tailTrace_4295818
  have hstable : (prefixWord ++ tailWord_4295818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295818).length < 2 ^ (prefixWord ++ tailWord_4295818).sum := by decide
  have hdescent : baseEnd_4295818 < baseStart_4295818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295824 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 3, 1, 3]
def baseStart_4295824 : Nat := 118140960795 + 4295824 * 2 ^ 59
def prefixEnd_4295824 : Nat := 4983230072969 + 3 ^ 40 * 4295824 * 2
def baseEnd_4295824 : Nat := 2205822519120105802543871

theorem tailTrace_4295824 : CollatzResearch.WordTrace tailWord_4295824 prefixEnd_4295824 2205822519120105802543871 := by
  unfold tailWord_4295824
  simp only [CollatzResearch.WordTrace]
  refine ⟨78340786594485395586995263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104454382125980527449327017 78340786594485395586995263)
  ·
    refine ⟨117511179891728093380492895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78340786594485395586995263 117511179891728093380492895)
    ·
      refine ⟨176266769837592140070739343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117511179891728093380492895 176266769837592140070739343)
      ·
        refine ⟨264400154756388210106109015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176266769837592140070739343 264400154756388210106109015)
        ·
          refine ⟨396600232134582315159163523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264400154756388210106109015 396600232134582315159163523)
          ·
            refine ⟨594900348201873472738745285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396600232134582315159163523 594900348201873472738745285)
            ·
              refine ⟨111543815287851276138514741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 594900348201873472738745285 111543815287851276138514741)
              ·
                refine ⟨10457232683236057137985757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111543815287851276138514741 10457232683236057137985757)
                ·
                  refine ⟨3921462256213521426744659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10457232683236057137985757 3921462256213521426744659)
                  ·
                    refine ⟨5882193384320282140116989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3921462256213521426744659 5882193384320282140116989)
                    ·
                      refine ⟨2205822519120105802543871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5882193384320282140116989 2205822519120105802543871)
                      ·
                        rfl

theorem cell23_4295824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_4295824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295824 prefixEnd_4295824 := by exact prefixLift 4295824
  have htrace : WordTrace (prefixWord ++ tailWord_4295824) baseStart_4295824 baseEnd_4295824 := by
    simpa [prefixWord, tailWord_4295824, baseEnd_4295824] using wordTrace_append hprefix tailTrace_4295824
  have hstable : (prefixWord ++ tailWord_4295824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295824).length < 2 ^ (prefixWord ++ tailWord_4295824).sum := by decide
  have hdescent : baseEnd_4295824 < baseStart_4295824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295831 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 6]
def baseStart_4295831 : Nat := 118140960795 + 4295831 * 2 ^ 59
def prefixEnd_4295831 : Nat := 4983230072969 + 3 ^ 40 * 4295831 * 2
def baseEnd_4295831 : Nat := 245091790387187475017371

theorem tailTrace_4295831 : CollatzResearch.WordTrace tailWord_4295831 prefixEnd_4295831 245091790387187475017371 := by
  unfold tailWord_4295831
  simp only [CollatzResearch.WordTrace]
  refine ⟨156681828499945431369495347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104454552333296954246330231 156681828499945431369495347)
  ·
    refine ⟨235022742749918147054243021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156681828499945431369495347 235022742749918147054243021)
    ·
      refine ⟨88133528531219305145341133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235022742749918147054243021 88133528531219305145341133)
      ·
        refine ⟨33050073199207239429502925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88133528531219305145341133 33050073199207239429502925)
        ·
          refine ⟨12393777449702714786063597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33050073199207239429502925 12393777449702714786063597)
          ·
            refine ⟨4647666543638518044773849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12393777449702714786063597 4647666543638518044773849)
            ·
              refine ⟨3485749907728888533580387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4647666543638518044773849 3485749907728888533580387)
              ·
                refine ⟨5228624861593332800370581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3485749907728888533580387 5228624861593332800370581)
                ·
                  refine ⟨245091790387187475017371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5228624861593332800370581 245091790387187475017371)
                  ·
                    rfl

theorem cell23_4295831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 6].length) (baseStart_4295831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295831 prefixEnd_4295831 := by exact prefixLift 4295831
  have htrace : WordTrace (prefixWord ++ tailWord_4295831) baseStart_4295831 baseEnd_4295831 := by
    simpa [prefixWord, tailWord_4295831, baseEnd_4295831] using wordTrace_append hprefix tailTrace_4295831
  have hstable : (prefixWord ++ tailWord_4295831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295831).length < 2 ^ (prefixWord ++ tailWord_4295831).sum := by decide
  have hdescent : baseEnd_4295831 < baseStart_4295831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295844 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_4295844 : Nat := 118140960795 + 4295844 * 2 ^ 59
def prefixEnd_4295844 : Nat := 4983230072969 + 3 ^ 40 * 4295844 * 2
def baseEnd_4295844 : Nat := 735277596244398574764593

theorem tailTrace_4295844 : CollatzResearch.WordTrace tailWord_4295844 prefixEnd_4295844 735277596244398574764593 := by
  unfold tailWord_4295844
  simp only [CollatzResearch.WordTrace]
  refine ⟨78341151324449167294859293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104454868432598889726479057 78341151324449167294859293)
  ·
    refine ⟨29377931746668437735572235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78341151324449167294859293 29377931746668437735572235)
    ·
      refine ⟨44066897620002656603358353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29377931746668437735572235 44066897620002656603358353)
      ·
        refine ⟨33050173215001992452518765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44066897620002656603358353 33050173215001992452518765)
        ·
          refine ⟨12393814955625747169694537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33050173215001992452518765 12393814955625747169694537)
          ·
            refine ⟨9295361216719310377270903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12393814955625747169694537 9295361216719310377270903)
            ·
              refine ⟨13943041825078965565906355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9295361216719310377270903 13943041825078965565906355)
              ·
                refine ⟨20914562737618448348859533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13943041825078965565906355 20914562737618448348859533)
                ·
                  refine ⟨7842961026606918130822325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20914562737618448348859533 7842961026606918130822325)
                  ·
                    refine ⟨735277596244398574764593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7842961026606918130822325 735277596244398574764593)
                    ·
                      rfl

theorem cell23_4295844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_4295844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295844 prefixEnd_4295844 := by exact prefixLift 4295844
  have htrace : WordTrace (prefixWord ++ tailWord_4295844) baseStart_4295844 baseEnd_4295844 := by
    simpa [prefixWord, tailWord_4295844, baseEnd_4295844] using wordTrace_append hprefix tailTrace_4295844
  have hstable : (prefixWord ++ tailWord_4295844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295844).length < 2 ^ (prefixWord ++ tailWord_4295844).sum := by decide
  have hdescent : baseEnd_4295844 < baseStart_4295844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295867 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5]
def baseStart_4295867 : Nat := 118140960795 + 4295867 * 2 ^ 59
def prefixEnd_4295867 : Nat := 4983230072969 + 3 ^ 40 * 4295867 * 2
def baseEnd_4295867 : Nat := 2205844598788249134306173

theorem tailTrace_4295867 : CollatzResearch.WordTrace tailWord_4295867 prefixEnd_4295867 2205844598788249134306173 := by
  unfold tailWord_4295867
  simp only [CollatzResearch.WordTrace]
  refine ⟨156683141527815009517805855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104455427685210006345203903 156683141527815009517805855)
  ·
    refine ⟨235024712291722514276708783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156683141527815009517805855 235024712291722514276708783)
    ·
      refine ⟨352537068437583771415063175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235024712291722514276708783 352537068437583771415063175)
      ·
        refine ⟨528805602656375657122594763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352537068437583771415063175 528805602656375657122594763)
        ·
          refine ⟨793208403984563485683892145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528805602656375657122594763 793208403984563485683892145)
          ·
            refine ⟨594906302988422614262919109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793208403984563485683892145 594906302988422614262919109)
            ·
              refine ⟨111544931810329240174297333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 594906302988422614262919109 111544931810329240174297333)
              ·
                refine ⟨10457337357218366266340375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111544931810329240174297333 10457337357218366266340375)
                ·
                  refine ⟨15686006035827549399510563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10457337357218366266340375 15686006035827549399510563)
                  ·
                    refine ⟨23529009053741324099265845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15686006035827549399510563 23529009053741324099265845)
                    ·
                      refine ⟨2205844598788249134306173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23529009053741324099265845 2205844598788249134306173)
                      ·
                        rfl

theorem cell23_4295867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].length) (baseStart_4295867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295867 prefixEnd_4295867 := by exact prefixLift 4295867
  have htrace : WordTrace (prefixWord ++ tailWord_4295867) baseStart_4295867 baseEnd_4295867 := by
    simpa [prefixWord, tailWord_4295867, baseEnd_4295867] using wordTrace_append hprefix tailTrace_4295867
  have hstable : (prefixWord ++ tailWord_4295867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295867).length < 2 ^ (prefixWord ++ tailWord_4295867).sum := by decide
  have hdescent : baseEnd_4295867 < baseStart_4295867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295877 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_4295877 : Nat := 118140960795 + 4295877 * 2 ^ 59
def prefixEnd_4295877 : Nat := 4983230072969 + 3 ^ 40 * 4295877 * 2
def baseEnd_4295877 : Nat := 2205849733594794095181127

theorem tailTrace_4295877 : CollatzResearch.WordTrace tailWord_4295877 prefixEnd_4295877 2205849733594794095181127 := by
  unfold tailWord_4295877
  simp only [CollatzResearch.WordTrace]
  refine ⟨156683506257778781225669885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104455670838519187483779923 156683506257778781225669885)
  ·
    refine ⟨58756314846667042959626207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156683506257778781225669885 58756314846667042959626207)
    ·
      refine ⟨88134472270000564439439311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58756314846667042959626207 88134472270000564439439311)
      ·
        refine ⟨132201708405000846659158967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88134472270000564439439311 132201708405000846659158967)
        ·
          refine ⟨198302562607501269988738451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132201708405000846659158967 198302562607501269988738451)
          ·
            refine ⟨297453843911251904983107677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198302562607501269988738451 297453843911251904983107677)
            ·
              refine ⟨111545191466719464368665379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297453843911251904983107677 111545191466719464368665379)
              ·
                refine ⟨167317787200079196552998069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111545191466719464368665379 167317787200079196552998069)
                ·
                  refine ⟨15686042550007424676843569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167317787200079196552998069 15686042550007424676843569)
                  ·
                    refine ⟨11764531912505568507632677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15686042550007424676843569 11764531912505568507632677)
                    ·
                      refine ⟨2205849733594794095181127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11764531912505568507632677 2205849733594794095181127)
                      ·
                        rfl

theorem cell23_4295877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_4295877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295877 prefixEnd_4295877 := by exact prefixLift 4295877
  have htrace : WordTrace (prefixWord ++ tailWord_4295877) baseStart_4295877 baseEnd_4295877 := by
    simpa [prefixWord, tailWord_4295877, baseEnd_4295877] using wordTrace_append hprefix tailTrace_4295877
  have hstable : (prefixWord ++ tailWord_4295877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295877).length < 2 ^ (prefixWord ++ tailWord_4295877).sum := by decide
  have hdescent : baseEnd_4295877 < baseStart_4295877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295904 : List Nat := [2, 1, 1, 3, 1, 5, 3, 7]
def baseStart_4295904 : Nat := 118140960795 + 4295904 * 2 ^ 59
def prefixEnd_4295904 : Nat := 4983230072969 + 3 ^ 40 * 4295904 * 2
def baseEnd_4295904 : Nat := 81698651761943166279389

theorem tailTrace_4295904 : CollatzResearch.WordTrace tailWord_4295904 prefixEnd_4295904 81698651761943166279389 := by
  unfold tailWord_4295904
  simp only [CollatzResearch.WordTrace]
  refine ⟨78342245514340482418451383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104456327352453976557935177 78342245514340482418451383)
  ·
    refine ⟨117513368271510723627677075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78342245514340482418451383 117513368271510723627677075)
    ·
      refine ⟨176270052407266085441515613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117513368271510723627677075 176270052407266085441515613)
      ·
        refine ⟨66101269652724782040568355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176270052407266085441515613 66101269652724782040568355)
        ·
          refine ⟨99151904479087173060852533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66101269652724782040568355 99151904479087173060852533)
          ·
            refine ⟨9295491044914422474454925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99151904479087173060852533 9295491044914422474454925)
            ·
              refine ⟨3485809141842908427920597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9295491044914422474454925 3485809141842908427920597)
              ·
                refine ⟨81698651761943166279389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3485809141842908427920597 81698651761943166279389)
                ·
                  rfl

theorem cell23_4295904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 7].length) (baseStart_4295904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295904 prefixEnd_4295904 := by exact prefixLift 4295904
  have htrace : WordTrace (prefixWord ++ tailWord_4295904) baseStart_4295904 baseEnd_4295904 := by
    simpa [prefixWord, tailWord_4295904, baseEnd_4295904] using wordTrace_append hprefix tailTrace_4295904
  have hstable : (prefixWord ++ tailWord_4295904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295904).length < 2 ^ (prefixWord ++ tailWord_4295904).sum := by decide
  have hdescent : baseEnd_4295904 < baseStart_4295904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295915 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 1, 2, 2]
def baseStart_4295915 : Nat := 118140960795 + 4295915 * 2 ^ 59
def prefixEnd_4295915 : Nat := 4983230072969 + 3 ^ 40 * 4295915 * 2
def baseEnd_4295915 : Nat := 2205869245859664946505953

theorem tailTrace_4295915 : CollatzResearch.WordTrace tailWord_4295915 prefixEnd_4295915 2205869245859664946505953 := by
  unfold tailWord_4295915
  simp only [CollatzResearch.WordTrace]
  refine ⟨156684892231641113715553199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104456594821094075810368799 156684892231641113715553199)
  ·
    refine ⟨235027338347461670573329799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156684892231641113715553199 235027338347461670573329799)
    ·
      refine ⟨352541007521192505859994699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235027338347461670573329799 352541007521192505859994699)
      ·
        refine ⟨528811511281788758789992049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352541007521192505859994699 528811511281788758789992049)
        ·
          refine ⟨396608633461341569092494037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528811511281788758789992049 396608633461341569092494037)
          ·
            refine ⟨9295514846750193025605329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 396608633461341569092494037 9295514846750193025605329)
            ·
              refine ⟨6971636135062644769203997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9295514846750193025605329 6971636135062644769203997)
              ·
                refine ⟨2614363550648491788451499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6971636135062644769203997 2614363550648491788451499)
                ·
                  refine ⟨3921545325972737682677249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614363550648491788451499 3921545325972737682677249)
                  ·
                    refine ⟨2941158994479553262007937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921545325972737682677249 2941158994479553262007937)
                    ·
                      refine ⟨2205869245859664946505953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941158994479553262007937 2205869245859664946505953)
                      ·
                        rfl

theorem cell23_4295915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 2, 2].length) (baseStart_4295915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295915 prefixEnd_4295915 := by exact prefixLift 4295915
  have htrace : WordTrace (prefixWord ++ tailWord_4295915) baseStart_4295915 baseEnd_4295915 := by
    simpa [prefixWord, tailWord_4295915, baseEnd_4295915] using wordTrace_append hprefix tailTrace_4295915
  have hstable : (prefixWord ++ tailWord_4295915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295915).length < 2 ^ (prefixWord ++ tailWord_4295915).sum := by decide
  have hdescent : baseEnd_4295915 < baseStart_4295915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295918 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_4295918 : Nat := 118140960795 + 4295918 * 2 ^ 59
def prefixEnd_4295918 : Nat := 4983230072969 + 3 ^ 40 * 4295918 * 2
def baseEnd_4295918 : Nat := 2205870786301628434768439

theorem tailTrace_4295918 : CollatzResearch.WordTrace tailWord_4295918 prefixEnd_4295918 2205870786301628434768439 := by
  unfold tailWord_4295918
  simp only [CollatzResearch.WordTrace]
  refine ⟨19585625206328780653489051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104456667767086830151941605 19585625206328780653489051)
  ·
    refine ⟨29378437809493170980233577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19585625206328780653489051 29378437809493170980233577)
    ·
      refine ⟨22033828357119878235175183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29378437809493170980233577 22033828357119878235175183)
      ·
        refine ⟨33050742535679817352762775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22033828357119878235175183 33050742535679817352762775)
        ·
          refine ⟨49576113803519726029144163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33050742535679817352762775 49576113803519726029144163)
          ·
            refine ⟨74364170705279589043716245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49576113803519726029144163 74364170705279589043716245)
            ·
              refine ⟨3485820501809980736424199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74364170705279589043716245 3485820501809980736424199)
              ·
                refine ⟨5228730752714971104636299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3485820501809980736424199 5228730752714971104636299)
                ·
                  refine ⟨7843096129072456656954449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5228730752714971104636299 7843096129072456656954449)
                  ·
                    refine ⟨5882322096804342492715837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7843096129072456656954449 5882322096804342492715837)
                    ·
                      refine ⟨2205870786301628434768439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5882322096804342492715837 2205870786301628434768439)
                      ·
                        rfl

theorem cell23_4295918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_4295918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295918 prefixEnd_4295918 := by exact prefixLift 4295918
  have htrace : WordTrace (prefixWord ++ tailWord_4295918) baseStart_4295918 baseEnd_4295918 := by
    simpa [prefixWord, tailWord_4295918, baseEnd_4295918] using wordTrace_append hprefix tailTrace_4295918
  have hstable : (prefixWord ++ tailWord_4295918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295918).length < 2 ^ (prefixWord ++ tailWord_4295918).sum := by decide
  have hdescent : baseEnd_4295918 < baseStart_4295918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295927 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_4295927 : Nat := 118140960795 + 4295927 * 2 ^ 59
def prefixEnd_4295927 : Nat := 4983230072969 + 3 ^ 40 * 4295927 * 2
def baseEnd_4295927 : Nat := 2205875407627518899555897

theorem tailTrace_4295927 : CollatzResearch.WordTrace tailWord_4295927 prefixEnd_4295927 2205875407627518899555897 := by
  unfold tailWord_4295927
  simp only [CollatzResearch.WordTrace]
  refine ⟨156685329907597639764990035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104456886605065093176660023 156685329907597639764990035)
  ·
    refine ⟨235027994861396459647485053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156685329907597639764990035 235027994861396459647485053)
    ·
      refine ⟨88135498073023672367806895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235027994861396459647485053 88135498073023672367806895)
      ·
        refine ⟨132203247109535508551710343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88135498073023672367806895 132203247109535508551710343)
        ·
          refine ⟨198304870664303262827565515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132203247109535508551710343 198304870664303262827565515)
          ·
            refine ⟨297457305996454894241348273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198304870664303262827565515 297457305996454894241348273)
            ·
              refine ⟨223092979497341170681011205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297457305996454894241348273 223092979497341170681011205)
              ·
                refine ⟨41829933655751469502689601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223092979497341170681011205 41829933655751469502689601)
                ·
                  refine ⟨31372450241813602127017201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41829933655751469502689601 31372450241813602127017201)
                  ·
                    refine ⟨23529337681360201595262901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31372450241813602127017201 23529337681360201595262901)
                    ·
                      refine ⟨2205875407627518899555897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23529337681360201595262901 2205875407627518899555897)
                      ·
                        rfl

theorem cell23_4295927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_4295927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295927 prefixEnd_4295927 := by exact prefixLift 4295927
  have htrace : WordTrace (prefixWord ++ tailWord_4295927) baseStart_4295927 baseEnd_4295927 := by
    simpa [prefixWord, tailWord_4295927, baseEnd_4295927] using wordTrace_append hprefix tailTrace_4295927
  have hstable : (prefixWord ++ tailWord_4295927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295927).length < 2 ^ (prefixWord ++ tailWord_4295927).sum := by decide
  have hdescent : baseEnd_4295927 < baseStart_4295927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4295966 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4295966 : Nat := 118140960795 + 4295966 * 2 ^ 59
def prefixEnd_4295966 : Nat := 4983230072969 + 3 ^ 40 * 4295966 * 2
def baseEnd_4295966 : Nat := 2205895433373044246968219

theorem tailTrace_4295966 : CollatzResearch.WordTrace tailWord_4295966 prefixEnd_4295966 2205895433373044246968219 := by
  unfold tailWord_4295966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19585844044307043678207469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104457834902970899617106501 19585844044307043678207469)
  ·
    refine ⟨7344691516615141379327801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19585844044307043678207469 7344691516615141379327801)
    ·
      refine ⟨5508518637461356034495851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7344691516615141379327801 5508518637461356034495851)
      ·
        refine ⟨8262777956192034051743777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5508518637461356034495851 8262777956192034051743777)
        ·
          refine ⟨6197083467144025538807833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262777956192034051743777 6197083467144025538807833)
          ·
            refine ⟨4647812600358019154105875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6197083467144025538807833 4647812600358019154105875)
            ·
              refine ⟨6971718900537028731158813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4647812600358019154105875 6971718900537028731158813)
              ·
                refine ⟨2614394587701385774184555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6971718900537028731158813 2614394587701385774184555)
                ·
                  refine ⟨3921591881552078661276833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614394587701385774184555 3921591881552078661276833)
                  ·
                    refine ⟨2941193911164058995957625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921591881552078661276833 2941193911164058995957625)
                    ·
                      refine ⟨2205895433373044246968219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941193911164058995957625 2205895433373044246968219)
                      ·
                        rfl

theorem cell23_4295966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4295966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4295966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4295966 prefixEnd_4295966 := by exact prefixLift 4295966
  have htrace : WordTrace (prefixWord ++ tailWord_4295966) baseStart_4295966 baseEnd_4295966 := by
    simpa [prefixWord, tailWord_4295966, baseEnd_4295966] using wordTrace_append hprefix tailTrace_4295966
  have hstable : (prefixWord ++ tailWord_4295966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4295966).length < 2 ^ (prefixWord ++ tailWord_4295966).sum := by decide
  have hdescent : baseEnd_4295966 < baseStart_4295966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4295966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296045 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 5]
def baseStart_4296045 : Nat := 118140960795 + 4296045 * 2 ^ 59
def prefixEnd_4296045 : Nat := 4983230072969 + 3 ^ 40 * 4296045 * 2
def baseEnd_4296045 : Nat := 245103999816083270875595

theorem tailTrace_4296045 : CollatzResearch.WordTrace tailWord_4296045 prefixEnd_4296045 245103999816083270875595 := by
  unfold tailWord_4296045
  simp only [CollatzResearch.WordTrace]
  refine ⟨156689633721170145917785589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104459755814113430611857059 156689633721170145917785589)
  ·
    refine ⟨14689653161359701179792399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156689633721170145917785589 14689653161359701179792399)
    ·
      refine ⟨22034479742039551769688599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14689653161359701179792399 22034479742039551769688599)
      ·
        refine ⟨33051719613059327654532899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22034479742039551769688599 33051719613059327654532899)
        ·
          refine ⟨49577579419588991481799349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33051719613059327654532899 49577579419588991481799349)
          ·
            refine ⟨4647898070586467951418689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49577579419588991481799349 4647898070586467951418689)
            ·
              refine ⟨3485923552939850963564017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4647898070586467951418689 3485923552939850963564017)
              ·
                refine ⟨2614442664704888222673013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485923552939850963564017 2614442664704888222673013)
                ·
                  refine ⟨245103999816083270875595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2614442664704888222673013 245103999816083270875595)
                  ·
                    rfl

theorem cell23_4296045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_4296045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296045 prefixEnd_4296045 := by exact prefixLift 4296045
  have htrace : WordTrace (prefixWord ++ tailWord_4296045) baseStart_4296045 baseEnd_4296045 := by
    simpa [prefixWord, tailWord_4296045, baseEnd_4296045] using wordTrace_append hprefix tailTrace_4296045
  have hstable : (prefixWord ++ tailWord_4296045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296045).length < 2 ^ (prefixWord ++ tailWord_4296045).sum := by decide
  have hdescent : baseEnd_4296045 < baseStart_4296045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296071 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 5, 4]
def baseStart_4296071 : Nat := 118140960795 + 4296071 * 2 ^ 59
def prefixEnd_4296071 : Nat := 4983230072969 + 3 ^ 40 * 4296071 * 2
def baseEnd_4296071 : Nat := 735316449613922112051745

theorem tailTrace_4296071 : CollatzResearch.WordTrace tailWord_4296071 prefixEnd_4296071 735316449613922112051745 := by
  unfold tailWord_4296071
  simp only [CollatzResearch.WordTrace]
  refine ⟨156690582019075952358232067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104460388012717301572154711 156690582019075952358232067)
  ·
    refine ⟨235035873028613928537348101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156690582019075952358232067 235035873028613928537348101)
    ·
      refine ⟨44069226192865111600752769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235035873028613928537348101 44069226192865111600752769)
      ·
        refine ⟨33051919644648833700564577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44069226192865111600752769 33051919644648833700564577)
        ·
          refine ⟨24788939733486625275423433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33051919644648833700564577 24788939733486625275423433)
          ·
            refine ⟨18591704800114968956567575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24788939733486625275423433 18591704800114968956567575)
            ·
              refine ⟨27887557200172453434851363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18591704800114968956567575 27887557200172453434851363)
              ·
                refine ⟨41831335800258680152277045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27887557200172453434851363 41831335800258680152277045)
                ·
                  refine ⟨3921687731274251264275973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41831335800258680152277045 3921687731274251264275973)
                  ·
                    refine ⟨735316449613922112051745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921687731274251264275973 735316449613922112051745)
                    ·
                      rfl

theorem cell23_4296071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_4296071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296071 prefixEnd_4296071 := by exact prefixLift 4296071
  have htrace : WordTrace (prefixWord ++ tailWord_4296071) baseStart_4296071 baseEnd_4296071 := by
    simpa [prefixWord, tailWord_4296071, baseEnd_4296071] using wordTrace_append hprefix tailTrace_4296071
  have hstable : (prefixWord ++ tailWord_4296071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296071).length < 2 ^ (prefixWord ++ tailWord_4296071).sum := by decide
  have hdescent : baseEnd_4296071 < baseStart_4296071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296078 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4296078 : Nat := 118140960795 + 4296078 * 2 ^ 59
def prefixEnd_4296078 : Nat := 4983230072969 + 3 ^ 40 * 4296078 * 2
def baseEnd_4296078 : Nat := 2205952943206347808767703

theorem tailTrace_4296078 : CollatzResearch.WordTrace tailWord_4296078 prefixEnd_4296078 2205952943206347808767703 := by
  unfold tailWord_4296078
  simp only [CollatzResearch.WordTrace]
  refine ⟨19586354666256324069217111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104460558220033728369157925 19586354666256324069217111)
  ·
    refine ⟨29379531999384486103825667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19586354666256324069217111 29379531999384486103825667)
    ·
      refine ⟨44069297999076729155738501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29379531999384486103825667 44069297999076729155738501)
      ·
        refine ⟨8262993374826886716700969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44069297999076729155738501 8262993374826886716700969)
        ·
          refine ⟨6197245031120165037525727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262993374826886716700969 6197245031120165037525727)
          ·
            refine ⟨9295867546680247556288591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6197245031120165037525727 9295867546680247556288591)
            ·
              refine ⟨13943801320020371334432887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9295867546680247556288591 13943801320020371334432887)
              ·
                refine ⟨20915701980030557001649331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13943801320020371334432887 20915701980030557001649331)
                ·
                  refine ⟨31373552970045835502473997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20915701980030557001649331 31373552970045835502473997)
                  ·
                    refine ⟨11765082363767188313427749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31373552970045835502473997 11765082363767188313427749)
                    ·
                      refine ⟨2205952943206347808767703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11765082363767188313427749 2205952943206347808767703)
                      ·
                        rfl

theorem cell23_4296078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4296078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296078 prefixEnd_4296078 := by exact prefixLift 4296078
  have htrace : WordTrace (prefixWord ++ tailWord_4296078) baseStart_4296078 baseEnd_4296078 := by
    simpa [prefixWord, tailWord_4296078, baseEnd_4296078] using wordTrace_append hprefix tailTrace_4296078
  have hstable : (prefixWord ++ tailWord_4296078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296078).length < 2 ^ (prefixWord ++ tailWord_4296078).sum := by decide
  have hdescent : baseEnd_4296078 < baseStart_4296078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296114 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_4296114 : Nat := 118140960795 + 4296114 * 2 ^ 59
def prefixEnd_4296114 : Nat := 4983230072969 + 3 ^ 40 * 4296114 * 2
def baseEnd_4296114 : Nat := 735323809503303222639179

theorem tailTrace_4296114 : CollatzResearch.WordTrace tailWord_4296114 prefixEnd_4296114 735323809503303222639179 := by
  unfold tailWord_4296114
  simp only [CollatzResearch.WordTrace]
  refine ⟨39173037589480042675511849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104461433571946780468031597 39173037589480042675511849)
  ·
    refine ⟨29379778192110032006633887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39173037589480042675511849 29379778192110032006633887)
    ·
      refine ⟨44069667288165048009950831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29379778192110032006633887 44069667288165048009950831)
      ·
        refine ⟨66104500932247572014926247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44069667288165048009950831 66104500932247572014926247)
        ·
          refine ⟨99156751398371358022389371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66104500932247572014926247 99156751398371358022389371)
          ·
            refine ⟨148735127097557037033584057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99156751398371358022389371 148735127097557037033584057)
            ·
              refine ⟨111551345323167777775188043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148735127097557037033584057 111551345323167777775188043)
              ·
                refine ⟨167327017984751666662782065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111551345323167777775188043 167327017984751666662782065)
                ·
                  refine ⟨125495263488563749997086549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167327017984751666662782065 125495263488563749997086549)
                  ·
                    refine ⟨735323809503303222639179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125495263488563749997086549 735323809503303222639179)
                    ·
                      rfl

theorem cell23_4296114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_4296114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296114 prefixEnd_4296114 := by exact prefixLift 4296114
  have htrace : WordTrace (prefixWord ++ tailWord_4296114) baseStart_4296114 baseEnd_4296114 := by
    simpa [prefixWord, tailWord_4296114, baseEnd_4296114] using wordTrace_append hprefix tailTrace_4296114
  have hstable : (prefixWord ++ tailWord_4296114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296114).length < 2 ^ (prefixWord ++ tailWord_4296114).sum := by decide
  have hdescent : baseEnd_4296114 < baseStart_4296114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296128 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 3, 1, 3]
def baseStart_4296128 : Nat := 118140960795 + 4296128 * 2 ^ 59
def prefixEnd_4296128 : Nat := 4983230072969 + 3 ^ 40 * 4296128 * 2
def baseEnd_4296128 : Nat := 2205978617239072613142473

theorem tailTrace_4296128 : CollatzResearch.WordTrace tailWord_4296128 prefixEnd_4296128 2205978617239072613142473 := by
  unfold tailWord_4296128
  simp only [CollatzResearch.WordTrace]
  refine ⟨78346330489934725546528519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104461773986579634062038025 78346330489934725546528519)
  ·
    refine ⟨117519495734902088319792779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78346330489934725546528519 117519495734902088319792779)
    ·
      refine ⟨176279243602353132479689169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117519495734902088319792779 176279243602353132479689169)
      ·
        refine ⟨132209432701764849359766877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176279243602353132479689169 132209432701764849359766877)
        ·
          refine ⟨49578537263161818509912579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132209432701764849359766877 49578537263161818509912579)
          ·
            refine ⟨74367805894742727764868869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49578537263161818509912579 74367805894742727764868869)
            ·
              refine ⟨13943963605264261455912913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74367805894742727764868869 13943963605264261455912913)
              ·
                refine ⟨10457972703948196091934685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13943963605264261455912913 10457972703948196091934685)
                ·
                  refine ⟨3921739763980573534475507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10457972703948196091934685 3921739763980573534475507)
                  ·
                    refine ⟨5882609645970860301713261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3921739763980573534475507 5882609645970860301713261)
                    ·
                      refine ⟨2205978617239072613142473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5882609645970860301713261 2205978617239072613142473)
                      ·
                        rfl

theorem cell23_4296128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_4296128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296128 prefixEnd_4296128 := by exact prefixLift 4296128
  have htrace : WordTrace (prefixWord ++ tailWord_4296128) baseStart_4296128 baseEnd_4296128 := by
    simpa [prefixWord, tailWord_4296128, baseEnd_4296128] using wordTrace_append hprefix tailTrace_4296128
  have hstable : (prefixWord ++ tailWord_4296128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296128).length < 2 ^ (prefixWord ++ tailWord_4296128).sum := by decide
  have hdescent : baseEnd_4296128 < baseStart_4296128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296131 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 1, 5]
def baseStart_4296131 : Nat := 118140960795 + 4296131 * 2 ^ 59
def prefixEnd_4296131 : Nat := 4983230072969 + 3 ^ 40 * 4296131 * 2
def baseEnd_4296131 : Nat := 735326719227012033801653

theorem tailTrace_4296131 : CollatzResearch.WordTrace tailWord_4296131 prefixEnd_4296131 735326719227012033801653 := by
  unfold tailWord_4296131
  simp only [CollatzResearch.WordTrace]
  refine ⟨156692770398858582605416247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104461846932572388403610831 156692770398858582605416247)
  ·
    refine ⟨235039155598287873908124371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156692770398858582605416247 235039155598287873908124371)
    ·
      refine ⟨352558733397431810862186557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235039155598287873908124371 352558733397431810862186557)
      ·
        refine ⟨132209525024036929073319959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352558733397431810862186557 132209525024036929073319959)
        ·
          refine ⟨198314287536055393609979939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132209525024036929073319959 198314287536055393609979939)
          ·
            refine ⟨297471431304083090414969909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198314287536055393609979939 297471431304083090414969909)
            ·
              refine ⟨27887946684757789726403429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 297471431304083090414969909 27887946684757789726403429)
              ·
                refine ⟨5228990003392085573700643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27887946684757789726403429 5228990003392085573700643)
                ·
                  refine ⟨7843485005088128360550965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5228990003392085573700643 7843485005088128360550965)
                  ·
                    refine ⟨735326719227012033801653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7843485005088128360550965 735326719227012033801653)
                    ·
                      rfl

theorem cell23_4296131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 5].length) (baseStart_4296131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296131 prefixEnd_4296131 := by exact prefixLift 4296131
  have htrace : WordTrace (prefixWord ++ tailWord_4296131) baseStart_4296131 baseEnd_4296131 := by
    simpa [prefixWord, tailWord_4296131, baseEnd_4296131] using wordTrace_append hprefix tailTrace_4296131
  have hstable : (prefixWord ++ tailWord_4296131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296131).length < 2 ^ (prefixWord ++ tailWord_4296131).sum := by decide
  have hdescent : baseEnd_4296131 < baseStart_4296131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296138 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_4296138 : Nat := 118140960795 + 4296138 * 2 ^ 59
def prefixEnd_4296138 : Nat := 4983230072969 + 3 ^ 40 * 4296138 * 2
def baseEnd_4296138 : Nat := 2205983752045617574017427

theorem tailTrace_4296138 : CollatzResearch.WordTrace tailWord_4296138 prefixEnd_4296138 2205983752045617574017427 := by
  unfold tailWord_4296138
  simp only [CollatzResearch.WordTrace]
  refine ⟨39173256427458305700230267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104462017139888815200614045 39173256427458305700230267)
  ·
    refine ⟨58759884641187458550345401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39173256427458305700230267 58759884641187458550345401)
    ·
      refine ⟨44069913480890593912759051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58759884641187458550345401 44069913480890593912759051)
      ·
        refine ⟨66104870221335890869138577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44069913480890593912759051 66104870221335890869138577)
        ·
          refine ⟨49578652666001918151853933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66104870221335890869138577 49578652666001918151853933)
          ·
            refine ⟨18591994749750719306945225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49578652666001918151853933 18591994749750719306945225)
            ·
              refine ⟨13943996062313039480208919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18591994749750719306945225 13943996062313039480208919)
              ·
                refine ⟨20915994093469559220313379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13943996062313039480208919 20915994093469559220313379)
                ·
                  refine ⟨31373991140204338830470069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20915994093469559220313379 31373991140204338830470069)
                  ·
                    refine ⟨2941311669394156765356569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31373991140204338830470069 2941311669394156765356569)
                    ·
                      refine ⟨2205983752045617574017427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941311669394156765356569 2205983752045617574017427)
                      ·
                        rfl

theorem cell23_4296138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_4296138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296138 prefixEnd_4296138 := by exact prefixLift 4296138
  have htrace : WordTrace (prefixWord ++ tailWord_4296138) baseStart_4296138 baseEnd_4296138 := by
    simpa [prefixWord, tailWord_4296138, baseEnd_4296138] using wordTrace_append hprefix tailTrace_4296138
  have hstable : (prefixWord ++ tailWord_4296138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296138).length < 2 ^ (prefixWord ++ tailWord_4296138).sum := by decide
  have hdescent : baseEnd_4296138 < baseStart_4296138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296221 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_4296221 : Nat := 118140960795 + 4296221 * 2 ^ 59
def prefixEnd_4296221 : Nat := 4983230072969 + 3 ^ 40 * 4296221 * 2
def baseEnd_4296221 : Nat := 735342123646646916426515

theorem tailTrace_4296221 : CollatzResearch.WordTrace tailWord_4296221 prefixEnd_4296221 735342123646646916426515 := by
  unfold tailWord_4296221
  simp only [CollatzResearch.WordTrace]
  refine ⟨156696052968532527976192517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104464035312355018650795011 156696052968532527976192517)
  ·
    refine ⟨29380509931599848995536097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156696052968532527976192517 29380509931599848995536097)
    ·
      refine ⟨22035382448699886746652073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29380509931599848995536097 22035382448699886746652073)
      ·
        refine ⟨16526536836524915059989055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22035382448699886746652073 16526536836524915059989055)
        ·
          refine ⟨24789805254787372589983583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16526536836524915059989055 24789805254787372589983583)
          ·
            refine ⟨37184707882181058884975375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24789805254787372589983583 37184707882181058884975375)
            ·
              refine ⟨55777061823271588327463063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37184707882181058884975375 55777061823271588327463063)
              ·
                refine ⟨83665592734907382491194595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55777061823271588327463063 83665592734907382491194595)
                ·
                  refine ⟨125498389102361073736791893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83665592734907382491194595 125498389102361073736791893)
                  ·
                    refine ⟨735342123646646916426515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125498389102361073736791893 735342123646646916426515)
                    ·
                      rfl

theorem cell23_4296221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_4296221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296221 prefixEnd_4296221 := by exact prefixLift 4296221
  have htrace : WordTrace (prefixWord ++ tailWord_4296221) baseStart_4296221 baseEnd_4296221 := by
    simpa [prefixWord, tailWord_4296221, baseEnd_4296221] using wordTrace_append hprefix tailTrace_4296221
  have hstable : (prefixWord ++ tailWord_4296221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296221).length < 2 ^ (prefixWord ++ tailWord_4296221).sum := by decide
  have hdescent : baseEnd_4296221 < baseStart_4296221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296241 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_4296241 : Nat := 118140960795 + 4296241 * 2 ^ 59
def prefixEnd_4296241 : Nat := 4983230072969 + 3 ^ 40 * 4296241 * 2
def baseEnd_4296241 : Nat := 2206036640553030671029453

theorem tailTrace_4296241 : CollatzResearch.WordTrace tailWord_4296241 prefixEnd_4296241 2206036640553030671029453 := by
  unfold tailWord_4296241
  simp only [CollatzResearch.WordTrace]
  refine ⟨156696782428460071391920577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104464521618973380927947051 156696782428460071391920577)
  ·
    refine ⟨117522586821345053543940433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156696782428460071391920577 117522586821345053543940433)
    ·
      refine ⟨88141940116008790157955325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117522586821345053543940433 88141940116008790157955325)
      ·
        refine ⟨33053227543503296309233247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88141940116008790157955325 33053227543503296309233247)
        ·
          refine ⟨49579841315254944463849871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33053227543503296309233247 49579841315254944463849871)
          ·
            refine ⟨74369761972882416695774807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49579841315254944463849871 74369761972882416695774807)
            ·
              refine ⟨111554642959323625043662211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74369761972882416695774807 111554642959323625043662211)
              ·
                refine ⟨167331964438985437565493317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111554642959323625043662211 167331964438985437565493317)
                ·
                  refine ⟨31374743332309769543529997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167331964438985437565493317 31374743332309769543529997)
                  ·
                    refine ⟨11765528749616163578823749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31374743332309769543529997 11765528749616163578823749)
                    ·
                      refine ⟨2206036640553030671029453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11765528749616163578823749 2206036640553030671029453)
                      ·
                        rfl

theorem cell23_4296241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_4296241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296241 prefixEnd_4296241 := by exact prefixLift 4296241
  have htrace : WordTrace (prefixWord ++ tailWord_4296241) baseStart_4296241 baseEnd_4296241 := by
    simpa [prefixWord, tailWord_4296241, baseEnd_4296241] using wordTrace_append hprefix tailTrace_4296241
  have hstable : (prefixWord ++ tailWord_4296241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296241).length < 2 ^ (prefixWord ++ tailWord_4296241).sum := by decide
  have hdescent : baseEnd_4296241 < baseStart_4296241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296245 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_4296245 : Nat := 118140960795 + 4296245 * 2 ^ 59
def prefixEnd_4296245 : Nat := 4983230072969 + 3 ^ 40 * 4296245 * 2
def baseEnd_4296245 : Nat := 2206038694475648655379435

theorem tailTrace_4296245 : CollatzResearch.WordTrace tailWord_4296245 prefixEnd_4296245 2206038694475648655379435 := by
  unfold tailWord_4296245
  simp only [CollatzResearch.WordTrace]
  refine ⟨156696928320445580075066189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104464618880297053383377459 156696928320445580075066189)
  ·
    refine ⟨58761348120167092528149821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156696928320445580075066189 58761348120167092528149821)
    ·
      refine ⟨22035505545062659698056183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58761348120167092528149821 22035505545062659698056183)
      ·
        refine ⟨33053258317593989547084275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22035505545062659698056183 33053258317593989547084275)
        ·
          refine ⟨49579887476390984320626413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33053258317593989547084275 49579887476390984320626413)
          ·
            refine ⟨18592457803646619120234905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49579887476390984320626413 18592457803646619120234905)
            ·
              refine ⟨13944343352734964340176179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18592457803646619120234905 13944343352734964340176179)
              ·
                refine ⟨20916515029102446510264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13944343352734964340176179 20916515029102446510264269)
                ·
                  refine ⟨7843693135913417441349101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20916515029102446510264269 7843693135913417441349101)
                  ·
                    refine ⟨2941384925967531540505913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7843693135913417441349101 2941384925967531540505913)
                    ·
                      refine ⟨2206038694475648655379435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941384925967531540505913 2206038694475648655379435)
                      ·
                        rfl

theorem cell23_4296245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_4296245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296245 prefixEnd_4296245 := by exact prefixLift 4296245
  have htrace : WordTrace (prefixWord ++ tailWord_4296245) baseStart_4296245 baseEnd_4296245 := by
    simpa [prefixWord, tailWord_4296245, baseEnd_4296245] using wordTrace_append hprefix tailTrace_4296245
  have hstable : (prefixWord ++ tailWord_4296245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296245).length < 2 ^ (prefixWord ++ tailWord_4296245).sum := by decide
  have hdescent : baseEnd_4296245 < baseStart_4296245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296261 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_4296261 : Nat := 118140960795 + 4296261 * 2 ^ 59
def prefixEnd_4296261 : Nat := 4983230072969 + 3 ^ 40 * 4296261 * 2
def baseEnd_4296261 : Nat := 2206046910166120592779361

theorem tailTrace_4296261 : CollatzResearch.WordTrace tailWord_4296261 prefixEnd_4296261 2206046910166120592779361 := by
  unfold tailWord_4296261
  simp only [CollatzResearch.WordTrace]
  refine ⟨156697511888387614807648637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104465007925591743205099091 156697511888387614807648637)
  ·
    refine ⟨58761566958145355552868239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156697511888387614807648637 58761566958145355552868239)
    ·
      refine ⟨88142350437218033329302359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58761566958145355552868239 88142350437218033329302359)
      ·
        refine ⟨132213525655827049993953539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88142350437218033329302359 132213525655827049993953539)
        ·
          refine ⟨198320288483740574990930309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132213525655827049993953539 198320288483740574990930309)
          ·
            refine ⟨37185054090701357810799433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198320288483740574990930309 37185054090701357810799433)
            ·
              refine ⟨27888790568026018358099575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37185054090701357810799433 27888790568026018358099575)
              ·
                refine ⟨41833185852039027537149363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27888790568026018358099575 41833185852039027537149363)
                ·
                  refine ⟨62749778778058541305724045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41833185852039027537149363 62749778778058541305724045)
                  ·
                    refine ⟨23531167041771952989646517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62749778778058541305724045 23531167041771952989646517)
                    ·
                      refine ⟨2206046910166120592779361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23531167041771952989646517 2206046910166120592779361)
                      ·
                        rfl

theorem cell23_4296261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_4296261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296261 prefixEnd_4296261 := by exact prefixLift 4296261
  have htrace : WordTrace (prefixWord ++ tailWord_4296261) baseStart_4296261 baseEnd_4296261 := by
    simpa [prefixWord, tailWord_4296261, baseEnd_4296261] using wordTrace_append hprefix tailTrace_4296261
  have hstable : (prefixWord ++ tailWord_4296261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296261).length < 2 ^ (prefixWord ++ tailWord_4296261).sum := by decide
  have hdescent : baseEnd_4296261 < baseStart_4296261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296292 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_4296292 : Nat := 118140960795 + 4296292 * 2 ^ 59
def prefixEnd_4296292 : Nat := 4983230072969 + 3 ^ 40 * 4296292 * 2
def baseEnd_4296292 : Nat := 2206062828066409971491719

theorem tailTrace_4296292 : CollatzResearch.WordTrace tailWord_4296292 prefixEnd_4296292 2206062828066409971491719 := by
  unfold tailWord_4296292
  simp only [CollatzResearch.WordTrace]
  refine ⟨78349321275637653551013565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104465761700850204734684753 78349321275637653551013565)
  ·
    refine ⟨29380995478364120081630087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78349321275637653551013565 29380995478364120081630087)
    ·
      refine ⟨44071493217546180122445131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29380995478364120081630087 44071493217546180122445131)
      ·
        refine ⟨66107239826319270183667697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44071493217546180122445131 66107239826319270183667697)
        ·
          refine ⟨49580429869739452637750773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66107239826319270183667697 49580429869739452637750773)
          ·
            refine ⟨4648165300288073684789135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49580429869739452637750773 4648165300288073684789135)
            ·
              refine ⟨6972247950432110527183703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648165300288073684789135 6972247950432110527183703)
              ·
                refine ⟨10458371925648165790775555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6972247950432110527183703 10458371925648165790775555)
                ·
                  refine ⟨15687557888472248686163333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10458371925648165790775555 15687557888472248686163333)
                  ·
                    refine ⟨2941417104088546628655625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15687557888472248686163333 2941417104088546628655625)
                    ·
                      refine ⟨2206062828066409971491719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941417104088546628655625 2206062828066409971491719)
                      ·
                        rfl

theorem cell23_4296292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_4296292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296292 prefixEnd_4296292 := by exact prefixLift 4296292
  have htrace : WordTrace (prefixWord ++ tailWord_4296292) baseStart_4296292 baseEnd_4296292 := by
    simpa [prefixWord, tailWord_4296292, baseEnd_4296292] using wordTrace_append hprefix tailTrace_4296292
  have hstable : (prefixWord ++ tailWord_4296292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296292).length < 2 ^ (prefixWord ++ tailWord_4296292).sum := by decide
  have hdescent : baseEnd_4296292 < baseStart_4296292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296298 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_4296298 : Nat := 118140960795 + 4296298 * 2 ^ 59
def prefixEnd_4296298 : Nat := 4983230072969 + 3 ^ 40 * 4296298 * 2
def baseEnd_4296298 : Nat := 245118434327815216446299

theorem tailTrace_4296298 : CollatzResearch.WordTrace tailWord_4296298 prefixEnd_4296298 245118434327815216446299 := by
  unfold tailWord_4296298
  simp only [CollatzResearch.WordTrace]
  refine ⟨39174715347313392531686387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104465907592835713417830365 39174715347313392531686387)
  ·
    refine ⟨58762073020970088797529581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39174715347313392531686387 58762073020970088797529581)
    ·
      refine ⟨22035777382863783299073593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58762073020970088797529581 22035777382863783299073593)
      ·
        refine ⟨16526833037147837474305195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22035777382863783299073593 16526833037147837474305195)
        ·
          refine ⟨24790249555721756211457793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16526833037147837474305195 24790249555721756211457793)
          ·
            refine ⟨18592687166791317158593345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24790249555721756211457793 18592687166791317158593345)
            ·
              refine ⟨13944515375093487868945009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18592687166791317158593345 13944515375093487868945009)
              ·
                refine ⟨10458386531320115901708757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13944515375093487868945009 10458386531320115901708757)
                ·
                  refine ⟨245118434327815216446299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10458386531320115901708757 245118434327815216446299)
                  ·
                    rfl

theorem cell23_4296298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_4296298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296298 prefixEnd_4296298 := by exact prefixLift 4296298
  have htrace : WordTrace (prefixWord ++ tailWord_4296298) baseStart_4296298 baseEnd_4296298 := by
    simpa [prefixWord, tailWord_4296298, baseEnd_4296298] using wordTrace_append hprefix tailTrace_4296298
  have hstable : (prefixWord ++ tailWord_4296298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296298).length < 2 ^ (prefixWord ++ tailWord_4296298).sum := by decide
  have hdescent : baseEnd_4296298 < baseStart_4296298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296368 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_4296368 : Nat := 118140960795 + 4296368 * 2 ^ 59
def prefixEnd_4296368 : Nat := 4983230072969 + 3 ^ 40 * 4296368 * 2
def baseEnd_4296368 : Nat := 2206101852596151674141369

theorem tailTrace_4296368 : CollatzResearch.WordTrace tailWord_4296368 prefixEnd_4296368 2206101852596151674141369 := by
  unfold tailWord_4296368
  simp only [CollatzResearch.WordTrace]
  refine ⟨78350707249499986040896879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104467609665999981387862505 78350707249499986040896879)
  ·
    refine ⟨117526060874249979061345319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78350707249499986040896879 117526060874249979061345319)
    ·
      refine ⟨176289091311374968592017979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117526060874249979061345319 176289091311374968592017979)
      ·
        refine ⟨264433636967062452888026969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176289091311374968592017979 264433636967062452888026969)
        ·
          refine ⟨198325227725296839666020227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264433636967062452888026969 198325227725296839666020227)
          ·
            refine ⟨297487841587945259499030341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198325227725296839666020227 297487841587945259499030341)
            ·
              refine ⟨55778970297739736156068189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297487841587945259499030341 55778970297739736156068189)
              ·
                refine ⟨20917113861652401058525571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55778970297739736156068189 20917113861652401058525571)
                ·
                  refine ⟨31375670792478601587788357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20917113861652401058525571 31375670792478601587788357)
                  ·
                    refine ⟨5882938273589737797710317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31375670792478601587788357 5882938273589737797710317)
                    ·
                      refine ⟨2206101852596151674141369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5882938273589737797710317 2206101852596151674141369)
                      ·
                        rfl

theorem cell23_4296368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_4296368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296368 prefixEnd_4296368 := by exact prefixLift 4296368
  have htrace : WordTrace (prefixWord ++ tailWord_4296368) baseStart_4296368 baseEnd_4296368 := by
    simpa [prefixWord, tailWord_4296368, baseEnd_4296368] using wordTrace_append hprefix tailTrace_4296368
  have hstable : (prefixWord ++ tailWord_4296368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296368).length < 2 ^ (prefixWord ++ tailWord_4296368).sum := by decide
  have hdescent : baseEnd_4296368 < baseStart_4296368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296392 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 1, 4]
def baseStart_4296392 : Nat := 118140960795 + 4296392 * 2 ^ 59
def prefixEnd_4296392 : Nat := 4983230072969 + 3 ^ 40 * 4296392 * 2
def baseEnd_4296392 : Nat := 735371392043953193413753

theorem tailTrace_4296392 : CollatzResearch.WordTrace tailWord_4296392 prefixEnd_4296392 735371392043953193413753 := by
  unfold tailWord_4296392
  simp only [CollatzResearch.WordTrace]
  refine ⟨78351144925456512090333715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104468193233942016120444953 78351144925456512090333715)
  ·
    refine ⟨117526717388184768135500573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78351144925456512090333715 117526717388184768135500573)
    ·
      refine ⟨44072519020569288050812715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117526717388184768135500573 44072519020569288050812715)
      ·
        refine ⟨66108778530853932076219073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44072519020569288050812715 66108778530853932076219073)
        ·
          refine ⟨49581583898140449057164305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66108778530853932076219073 49581583898140449057164305)
          ·
            refine ⟨37186187923605336792873229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49581583898140449057164305 37186187923605336792873229)
            ·
              refine ⟨13944820471352001297327461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37186187923605336792873229 13944820471352001297327461)
              ·
                refine ⟨2614653838378500243248899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13944820471352001297327461 2614653838378500243248899)
                ·
                  refine ⟨3921980757567750364873349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614653838378500243248899 3921980757567750364873349)
                  ·
                    refine ⟨735371392043953193413753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921980757567750364873349 735371392043953193413753)
                    ·
                      rfl

theorem cell23_4296392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_4296392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296392 prefixEnd_4296392 := by exact prefixLift 4296392
  have htrace : WordTrace (prefixWord ++ tailWord_4296392) baseStart_4296392 baseEnd_4296392 := by
    simpa [prefixWord, tailWord_4296392, baseEnd_4296392] using wordTrace_append hprefix tailTrace_4296392
  have hstable : (prefixWord ++ tailWord_4296392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296392).length < 2 ^ (prefixWord ++ tailWord_4296392).sum := by decide
  have hdescent : baseEnd_4296392 < baseStart_4296392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296419 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4296419 : Nat := 118140960795 + 4296419 * 2 ^ 59
def prefixEnd_4296419 : Nat := 4983230072969 + 3 ^ 40 * 4296419 * 2
def baseEnd_4296419 : Nat := 2206128040109530974603635

theorem tailTrace_4296419 : CollatzResearch.WordTrace tailWord_4296419 prefixEnd_4296419 2206128040109530974603635 := by
  unfold tailWord_4296419
  simp only [CollatzResearch.WordTrace]
  refine ⟨156703274621815207791900311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104468849747876805194600207 156703274621815207791900311)
  ·
    refine ⟨235054911932722811687850467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156703274621815207791900311 235054911932722811687850467)
    ·
      refine ⟨352582367899084217531775701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235054911932722811687850467 352582367899084217531775701)
      ·
        refine ⟨8263649247634786348400993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 352582367899084217531775701 8263649247634786348400993)
        ·
          refine ⟨6197736935726089761300745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8263649247634786348400993 6197736935726089761300745)
          ·
            refine ⟨4648302701794567320975559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6197736935726089761300745 4648302701794567320975559)
            ·
              refine ⟨6972454052691850981463339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648302701794567320975559 6972454052691850981463339)
              ·
                refine ⟨10458681079037776472195009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6972454052691850981463339 10458681079037776472195009)
                ·
                  refine ⟨7844010809278332354146257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10458681079037776472195009 7844010809278332354146257)
                  ·
                    refine ⟨5883008106958749265609693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7844010809278332354146257 5883008106958749265609693)
                    ·
                      refine ⟨2206128040109530974603635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5883008106958749265609693 2206128040109530974603635)
                      ·
                        rfl

theorem cell23_4296419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4296419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296419 prefixEnd_4296419 := by exact prefixLift 4296419
  have htrace : WordTrace (prefixWord ++ tailWord_4296419) baseStart_4296419 baseEnd_4296419 := by
    simpa [prefixWord, tailWord_4296419, baseEnd_4296419] using wordTrace_append hprefix tailTrace_4296419
  have hstable : (prefixWord ++ tailWord_4296419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296419).length < 2 ^ (prefixWord ++ tailWord_4296419).sum := by decide
  have hdescent : baseEnd_4296419 < baseStart_4296419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296449 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_4296449 : Nat := 118140960795 + 4296449 * 2 ^ 59
def prefixEnd_4296449 : Nat := 4983230072969 + 3 ^ 40 * 4296449 * 2
def baseEnd_4296449 : Nat := 2206143444529165857228497

theorem tailTrace_4296449 : CollatzResearch.WordTrace tailWord_4296449 prefixEnd_4296449 2206143444529165857228497 := by
  unfold tailWord_4296449
  simp only [CollatzResearch.WordTrace]
  refine ⟨156704368811706522915492401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104469579207804348610328267 156704368811706522915492401)
  ·
    refine ⟨117528276608779892186619301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156704368811706522915492401 117528276608779892186619301)
    ·
      refine ⟨22036551864146229784991119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117528276608779892186619301 22036551864146229784991119)
      ·
        refine ⟨33054827796219344677486679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22036551864146229784991119 33054827796219344677486679)
        ·
          refine ⟨49582241694329017016230019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33054827796219344677486679 49582241694329017016230019)
          ·
            refine ⟨74373362541493525524345029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49582241694329017016230019 74373362541493525524345029)
            ·
              refine ⟨13945005476530036035814693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74373362541493525524345029 13945005476530036035814693)
              ·
                refine ⟨2614688526849381756715255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13945005476530036035814693 2614688526849381756715255)
                ·
                  refine ⟨3922032790274072635072883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614688526849381756715255 3922032790274072635072883)
                  ·
                    refine ⟨5883049185411108952609325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3922032790274072635072883 5883049185411108952609325)
                    ·
                      refine ⟨2206143444529165857228497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5883049185411108952609325 2206143444529165857228497)
                      ·
                        rfl

theorem cell23_4296449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_4296449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296449 prefixEnd_4296449 := by exact prefixLift 4296449
  have htrace : WordTrace (prefixWord ++ tailWord_4296449) baseStart_4296449 baseEnd_4296449 := by
    simpa [prefixWord, tailWord_4296449, baseEnd_4296449] using wordTrace_append hprefix tailTrace_4296449
  have hstable : (prefixWord ++ tailWord_4296449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296449).length < 2 ^ (prefixWord ++ tailWord_4296449).sum := by decide
  have hdescent : baseEnd_4296449 < baseStart_4296449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296492 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_4296492 : Nat := 118140960795 + 4296492 * 2 ^ 59
def prefixEnd_4296492 : Nat := 4983230072969 + 3 ^ 40 * 4296492 * 2
def baseEnd_4296492 : Nat := 2206165524197309188990799

theorem tailTrace_4296492 : CollatzResearch.WordTrace tailWord_4296492 prefixEnd_4296492 2206165524197309188990799 := by
  unfold tailWord_4296492
  simp only [CollatzResearch.WordTrace]
  refine ⟨78352968575275370629653865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104470624767033827506205153 78352968575275370629653865)
  ·
    refine ⟨58764726431456527972240399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78352968575275370629653865 58764726431456527972240399)
    ·
      refine ⟨88147089647184791958360599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58764726431456527972240399 88147089647184791958360599)
      ·
        refine ⟨132220634470777187937540899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88147089647184791958360599 132220634470777187937540899)
        ·
          refine ⟨198330951706165781906311349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132220634470777187937540899 198330951706165781906311349)
          ·
            refine ⟨18593526722453042053716689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198330951706165781906311349 18593526722453042053716689)
            ·
              refine ⟨13945145041839781540287517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18593526722453042053716689 13945145041839781540287517)
              ·
                refine ⟨5229429390689918077607819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13945145041839781540287517 5229429390689918077607819)
                ·
                  refine ⟨7844144086034877116411729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5229429390689918077607819 7844144086034877116411729)
                  ·
                    refine ⟨5883108064526157837308797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7844144086034877116411729 5883108064526157837308797)
                    ·
                      refine ⟨2206165524197309188990799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5883108064526157837308797 2206165524197309188990799)
                      ·
                        rfl

theorem cell23_4296492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_4296492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296492 prefixEnd_4296492 := by exact prefixLift 4296492
  have htrace : WordTrace (prefixWord ++ tailWord_4296492) baseStart_4296492 baseEnd_4296492 := by
    simpa [prefixWord, tailWord_4296492, baseEnd_4296492] using wordTrace_append hprefix tailTrace_4296492
  have hstable : (prefixWord ++ tailWord_4296492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296492).length < 2 ^ (prefixWord ++ tailWord_4296492).sum := by decide
  have hdescent : baseEnd_4296492 < baseStart_4296492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296502 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4296502 : Nat := 118140960795 + 4296502 * 2 ^ 59
def prefixEnd_4296502 : Nat := 4983230072969 + 3 ^ 40 * 4296502 * 2
def baseEnd_4296502 : Nat := 2206170659003854149865753

theorem tailTrace_4296502 : CollatzResearch.WordTrace tailWord_4296502 prefixEnd_4296502 2206170659003854149865753 := by
  unfold tailWord_4296502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794143867532157060448235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104470867920343008644781173 9794143867532157060448235)
  ·
    refine ⟨14691215801298235590672353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9794143867532157060448235 14691215801298235590672353)
    ·
      refine ⟨11018411850973676693004265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14691215801298235590672353 11018411850973676693004265)
      ·
        refine ⟨8263808888230257519753199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11018411850973676693004265 8263808888230257519753199)
        ·
          refine ⟨12395713332345386279629799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8263808888230257519753199 12395713332345386279629799)
          ·
            refine ⟨18593569998518079419444699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12395713332345386279629799 18593569998518079419444699)
            ·
              refine ⟨27890354997777119129167049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18593569998518079419444699 27890354997777119129167049)
              ·
                refine ⟨20917766248332839346875287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27890354997777119129167049 20917766248332839346875287)
                ·
                  refine ⟨31376649372499259020312931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20917766248332839346875287 31376649372499259020312931)
                  ·
                    refine ⟨47064974058748888530469397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31376649372499259020312931 47064974058748888530469397)
                    ·
                      refine ⟨2206170659003854149865753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47064974058748888530469397 2206170659003854149865753)
                      ·
                        rfl

theorem cell23_4296502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4296502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296502 prefixEnd_4296502 := by exact prefixLift 4296502
  have htrace : WordTrace (prefixWord ++ tailWord_4296502) baseStart_4296502 baseEnd_4296502 := by
    simpa [prefixWord, tailWord_4296502, baseEnd_4296502] using wordTrace_append hprefix tailTrace_4296502
  have hstable : (prefixWord ++ tailWord_4296502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296502).length < 2 ^ (prefixWord ++ tailWord_4296502).sum := by decide
  have hdescent : baseEnd_4296502 < baseStart_4296502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296506 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2]
def baseStart_4296506 : Nat := 118140960795 + 4296506 * 2 ^ 59
def prefixEnd_4296506 : Nat := 4983230072969 + 3 ^ 40 * 4296506 * 2
def baseEnd_4296506 : Nat := 2206172712926472134215735

theorem tailTrace_4296506 : CollatzResearch.WordTrace tailWord_4296506 prefixEnd_4296506 2206172712926472134215735 := by
  unfold tailWord_4296506
  simp only [CollatzResearch.WordTrace]
  refine ⟨39176611943125005412579343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104470965181666681100211581 39176611943125005412579343)
  ·
    refine ⟨58764917914687508118869015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39176611943125005412579343 58764917914687508118869015)
    ·
      refine ⟨88147376872031262178303523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58764917914687508118869015 88147376872031262178303523)
      ·
        refine ⟨132221065308046893267455285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88147376872031262178303523 132221065308046893267455285)
        ·
          refine ⟨12395724872629396243823933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132221065308046893267455285 12395724872629396243823933)
          ·
            refine ⟨4648396827236023591433975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12395724872629396243823933 4648396827236023591433975)
            ·
              refine ⟨6972595240854035387150963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648396827236023591433975 6972595240854035387150963)
              ·
                refine ⟨10458892861281053080726445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6972595240854035387150963 10458892861281053080726445)
                ·
                  refine ⟨3922084822980394905272417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10458892861281053080726445 3922084822980394905272417)
                  ·
                    refine ⟨2941563617235296178954313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3922084822980394905272417 2941563617235296178954313)
                    ·
                      refine ⟨2206172712926472134215735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941563617235296178954313 2206172712926472134215735)
                      ·
                        rfl

theorem cell23_4296506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_4296506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296506 prefixEnd_4296506 := by exact prefixLift 4296506
  have htrace : WordTrace (prefixWord ++ tailWord_4296506) baseStart_4296506 baseEnd_4296506 := by
    simpa [prefixWord, tailWord_4296506, baseEnd_4296506] using wordTrace_append hprefix tailTrace_4296506
  have hstable : (prefixWord ++ tailWord_4296506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296506).length < 2 ^ (prefixWord ++ tailWord_4296506).sum := by decide
  have hdescent : baseEnd_4296506 < baseStart_4296506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296528 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_4296528 : Nat := 118140960795 + 4296528 * 2 ^ 59
def prefixEnd_4296528 : Nat := 4983230072969 + 3 ^ 40 * 4296528 * 2
def baseEnd_4296528 : Nat := 2206184009500871048140633

theorem tailTrace_4296528 : CollatzResearch.WordTrace tailWord_4296528 prefixEnd_4296528 2206184009500871048140633 := by
  unfold tailWord_4296528
  simp only [CollatzResearch.WordTrace]
  refine ⟨78353625089210159703809119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104471500118946879605078825 78353625089210159703809119)
  ·
    refine ⟨117530437633815239555713679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78353625089210159703809119 117530437633815239555713679)
    ·
      refine ⟨176295656450722859333570519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117530437633815239555713679 176295656450722859333570519)
      ·
        refine ⟨264443484676084289000355779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176295656450722859333570519 264443484676084289000355779)
        ·
          refine ⟨396665227014126433500533669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264443484676084289000355779 396665227014126433500533669)
          ·
            refine ⟨74374730065148706281350063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 396665227014126433500533669 74374730065148706281350063)
            ·
              refine ⟨111562095097723059422025095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74374730065148706281350063 111562095097723059422025095)
              ·
                refine ⟨167343142646584589133037643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111562095097723059422025095 167343142646584589133037643)
                ·
                  refine ⟨251014713969876883699556465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167343142646584589133037643 251014713969876883699556465)
                  ·
                    refine ⟨188261035477407662774667349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251014713969876883699556465 188261035477407662774667349)
                    ·
                      refine ⟨2206184009500871048140633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 188261035477407662774667349 2206184009500871048140633)
                      ·
                        rfl

theorem cell23_4296528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_4296528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296528 prefixEnd_4296528 := by exact prefixLift 4296528
  have htrace : WordTrace (prefixWord ++ tailWord_4296528) baseStart_4296528 baseEnd_4296528 := by
    simpa [prefixWord, tailWord_4296528, baseEnd_4296528] using wordTrace_append hprefix tailTrace_4296528
  have hstable : (prefixWord ++ tailWord_4296528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296528).length < 2 ^ (prefixWord ++ tailWord_4296528).sum := by decide
  have hdescent : baseEnd_4296528 < baseStart_4296528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296562 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_4296562 : Nat := 118140960795 + 4296562 * 2 ^ 59
def prefixEnd_4296562 : Nat := 4983230072969 + 3 ^ 40 * 4296562 * 2
def baseEnd_4296562 : Nat := 2206201467843123915115477

theorem tailTrace_4296562 : CollatzResearch.WordTrace tailWord_4296562 prefixEnd_4296562 2206201467843123915115477 := by
  unfold tailWord_4296562
  simp only [CollatzResearch.WordTrace]
  refine ⟨39177122565074285803588985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104472326840198095476237293 39177122565074285803588985)
  ·
    refine ⟨29382841923805714352691739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39177122565074285803588985 29382841923805714352691739)
    ·
      refine ⟨44074262885708571529037609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29382841923805714352691739 44074262885708571529037609)
      ·
        refine ⟨33055697164281428646778207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44074262885708571529037609 33055697164281428646778207)
        ·
          refine ⟨49583545746422142970167311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33055697164281428646778207 49583545746422142970167311)
          ·
            refine ⟨74375318619633214455250967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49583545746422142970167311 74375318619633214455250967)
            ·
              refine ⟨111562977929449821682876451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74375318619633214455250967 111562977929449821682876451)
              ·
                refine ⟨167344466894174732524314677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111562977929449821682876451 167344466894174732524314677)
                ·
                  refine ⟨15688543771328881174154501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167344466894174732524314677 15688543771328881174154501)
                  ·
                    refine ⟨2941601957124165220153969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15688543771328881174154501 2941601957124165220153969)
                    ·
                      refine ⟨2206201467843123915115477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941601957124165220153969 2206201467843123915115477)
                      ·
                        rfl

theorem cell23_4296562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_4296562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296562 prefixEnd_4296562 := by exact prefixLift 4296562
  have htrace : WordTrace (prefixWord ++ tailWord_4296562) baseStart_4296562 baseEnd_4296562 := by
    simpa [prefixWord, tailWord_4296562, baseEnd_4296562] using wordTrace_append hprefix tailTrace_4296562
  have hstable : (prefixWord ++ tailWord_4296562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296562).length < 2 ^ (prefixWord ++ tailWord_4296562).sum := by decide
  have hdescent : baseEnd_4296562 < baseStart_4296562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296579 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 1, 4, 2]
def baseStart_4296579 : Nat := 118140960795 + 4296579 * 2 ^ 59
def prefixEnd_4296579 : Nat := 4983230072969 + 3 ^ 40 * 4296579 * 2
def baseEnd_4296579 : Nat := 2206210197014250348602899

theorem tailTrace_4296579 : CollatzResearch.WordTrace tailWord_4296579 prefixEnd_4296579 2206210197014250348602899 := by
  unfold tailWord_4296579
  simp only [CollatzResearch.WordTrace]
  refine ⟨156709110301235555117724791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104472740200823703411816527 156709110301235555117724791)
  ·
    refine ⟨235063665451853332676587187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156709110301235555117724791 235063665451853332676587187)
    ·
      refine ⟨352595498177779999014880781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235063665451853332676587187 352595498177779999014880781)
      ·
        refine ⟨132223311816667499630580293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352595498177779999014880781 132223311816667499630580293)
        ·
          refine ⟨24791870965625156180733805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132223311816667499630580293 24791870965625156180733805)
          ·
            refine ⟨9296951612109433567775177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24791870965625156180733805 9296951612109433567775177)
            ·
              refine ⟨6972713709082075175831383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9296951612109433567775177 6972713709082075175831383)
              ·
                refine ⟨10459070563623112763747075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6972713709082075175831383 10459070563623112763747075)
                ·
                  refine ⟨15688605845434669145620613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10459070563623112763747075 15688605845434669145620613)
                  ·
                    refine ⟨2941613596019000464803865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15688605845434669145620613 2941613596019000464803865)
                    ·
                      refine ⟨2206210197014250348602899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941613596019000464803865 2206210197014250348602899)
                      ·
                        rfl

theorem cell23_4296579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_4296579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296579 prefixEnd_4296579 := by exact prefixLift 4296579
  have htrace : WordTrace (prefixWord ++ tailWord_4296579) baseStart_4296579 baseEnd_4296579 := by
    simpa [prefixWord, tailWord_4296579, baseEnd_4296579] using wordTrace_append hprefix tailTrace_4296579
  have hstable : (prefixWord ++ tailWord_4296579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296579).length < 2 ^ (prefixWord ++ tailWord_4296579).sum := by decide
  have hdescent : baseEnd_4296579 < baseStart_4296579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296585 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 7]
def baseStart_4296585 : Nat := 118140960795 + 4296585 * 2 ^ 59
def prefixEnd_4296585 : Nat := 4983230072969 + 3 ^ 40 * 4296585 * 2
def baseEnd_4296585 : Nat := 245134808655353036125319

theorem tailTrace_4296585 : CollatzResearch.WordTrace tailWord_4296585 prefixEnd_4296585 245134808655353036125319 := by
  unfold tailWord_4296585
  simp only [CollatzResearch.WordTrace]
  refine ⟨156709329139213818142443209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104472886092809212094962139 156709329139213818142443209)
  ·
    refine ⟨117531996854410363606832407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156709329139213818142443209 117531996854410363606832407)
    ·
      refine ⟨176297995281615545410248611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117531996854410363606832407 176297995281615545410248611)
      ·
        refine ⟨264446992922423318115372917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176297995281615545410248611 264446992922423318115372917)
        ·
          refine ⟨24791905586477186073316211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264446992922423318115372917 24791905586477186073316211)
          ·
            refine ⟨37187858379715779109974317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24791905586477186073316211 37187858379715779109974317)
            ·
              refine ⟨13945446892393417166240369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37187858379715779109974317 13945446892393417166240369)
              ·
                refine ⟨10459085169295062874680277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13945446892393417166240369 10459085169295062874680277)
                ·
                  refine ⟨245134808655353036125319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10459085169295062874680277 245134808655353036125319)
                  ·
                    rfl

theorem cell23_4296585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_4296585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296585 prefixEnd_4296585 := by exact prefixLift 4296585
  have htrace : WordTrace (prefixWord ++ tailWord_4296585) baseStart_4296585 baseEnd_4296585 := by
    simpa [prefixWord, tailWord_4296585, baseEnd_4296585] using wordTrace_append hprefix tailTrace_4296585
  have hstable : (prefixWord ++ tailWord_4296585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296585).length < 2 ^ (prefixWord ++ tailWord_4296585).sum := by decide
  have hdescent : baseEnd_4296585 < baseStart_4296585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296600 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4296600 : Nat := 118140960795 + 4296600 * 2 ^ 59
def prefixEnd_4296600 : Nat := 4983230072969 + 3 ^ 40 * 4296600 * 2
def baseEnd_4296600 : Nat := 2206220980107994766440303

theorem tailTrace_4296600 : CollatzResearch.WordTrace tailWord_4296600 prefixEnd_4296600 2206220980107994766440303 := by
  unfold tailWord_4296600
  simp only [CollatzResearch.WordTrace]
  refine ⟨78354938117079737852119627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104473250822772983802826169 78354938117079737852119627)
  ·
    refine ⟨117532407175619606778179441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78354938117079737852119627 117532407175619606778179441)
    ·
      refine ⟨88149305381714705083634581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117532407175619606778179441 88149305381714705083634581)
      ·
        refine ⟨4131998689767876800795371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88149305381714705083634581 4131998689767876800795371)
        ·
          refine ⟨6197998034651815201193057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131998689767876800795371 6197998034651815201193057)
          ·
            refine ⟨4648498525988861400894793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6197998034651815201193057 4648498525988861400894793)
            ·
              refine ⟨3486373894491646050671095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4648498525988861400894793 3486373894491646050671095)
              ·
                refine ⟨5229560841737469076006643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486373894491646050671095 5229560841737469076006643)
                ·
                  refine ⟨7844341262606203614009965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5229560841737469076006643 7844341262606203614009965)
                  ·
                    refine ⟨2941627973477326355253737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7844341262606203614009965 2941627973477326355253737)
                    ·
                      refine ⟨2206220980107994766440303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941627973477326355253737 2206220980107994766440303)
                      ·
                        rfl

theorem cell23_4296600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4296600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296600 prefixEnd_4296600 := by exact prefixLift 4296600
  have htrace : WordTrace (prefixWord ++ tailWord_4296600) baseStart_4296600 baseEnd_4296600 := by
    simpa [prefixWord, tailWord_4296600, baseEnd_4296600] using wordTrace_append hprefix tailTrace_4296600
  have hstable : (prefixWord ++ tailWord_4296600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296600).length < 2 ^ (prefixWord ++ tailWord_4296600).sum := by decide
  have hdescent : baseEnd_4296600 < baseStart_4296600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296612 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_4296612 : Nat := 118140960795 + 4296612 * 2 ^ 59
def prefixEnd_4296612 : Nat := 4983230072969 + 3 ^ 40 * 4296612 * 2
def baseEnd_4296612 : Nat := 2206227141875848719490247

theorem tailTrace_4296612 : CollatzResearch.WordTrace tailWord_4296612 prefixEnd_4296612 2206227141875848719490247 := by
  unfold tailWord_4296612
  simp only [CollatzResearch.WordTrace]
  refine ⟨78355156955058000876838045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104473542606744001169117393 78355156955058000876838045)
  ·
    refine ⟨29383183858146750328814267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78355156955058000876838045 29383183858146750328814267)
    ·
      refine ⟨44074775787220125493221401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29383183858146750328814267 44074775787220125493221401)
      ·
        refine ⟨33056081840415094119916051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44074775787220125493221401 33056081840415094119916051)
        ·
          refine ⟨49584122760622641179874077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33056081840415094119916051 49584122760622641179874077)
          ·
            refine ⟨18594046035233490442452779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49584122760622641179874077 18594046035233490442452779)
            ·
              refine ⟨27891069052850235663679169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18594046035233490442452779 27891069052850235663679169)
              ·
                refine ⟨20918301789637676747759377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27891069052850235663679169 20918301789637676747759377)
                ·
                  refine ⟨15688726342228257560819533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20918301789637676747759377 15688726342228257560819533)
                  ·
                    refine ⟨5883272378335596585307325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15688726342228257560819533 5883272378335596585307325)
                    ·
                      refine ⟨2206227141875848719490247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5883272378335596585307325 2206227141875848719490247)
                      ·
                        rfl

theorem cell23_4296612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_4296612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296612 prefixEnd_4296612 := by exact prefixLift 4296612
  have htrace : WordTrace (prefixWord ++ tailWord_4296612) baseStart_4296612 baseEnd_4296612 := by
    simpa [prefixWord, tailWord_4296612, baseEnd_4296612] using wordTrace_append hprefix tailTrace_4296612
  have hstable : (prefixWord ++ tailWord_4296612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296612).length < 2 ^ (prefixWord ++ tailWord_4296612).sum := by decide
  have hdescent : baseEnd_4296612 < baseStart_4296612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296635 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4]
def baseStart_4296635 : Nat := 118140960795 + 4296635 * 2 ^ 59
def prefixEnd_4296635 : Nat := 4983230072969 + 3 ^ 40 * 4296635 * 2
def baseEnd_4296635 : Nat := 2206238951930902129502641

theorem tailTrace_4296635 : CollatzResearch.WordTrace tailWord_4296635 prefixEnd_4296635 2206238951930902129502641 := by
  unfold tailWord_4296635
  simp only [CollatzResearch.WordTrace]
  refine ⟨156711152789032676681763359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104474101859355117787842239 156711152789032676681763359)
  ·
    refine ⟨235066729183549015022645039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156711152789032676681763359 235066729183549015022645039)
    ·
      refine ⟨352600093775323522533967559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235066729183549015022645039 352600093775323522533967559)
      ·
        refine ⟨528900140662985283800951339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352600093775323522533967559 528900140662985283800951339)
        ·
          refine ⟨793350210994477925701427009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528900140662985283800951339 793350210994477925701427009)
          ·
            refine ⟨595012658245858444276070257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793350210994477925701427009 595012658245858444276070257)
            ·
              refine ⟨446259493684393833207052693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595012658245858444276070257 446259493684393833207052693)
              ·
                refine ⟨20918413766455960931580595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 446259493684393833207052693 20918413766455960931580595)
                ·
                  refine ⟨31377620649683941397370893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20918413766455960931580595 31377620649683941397370893)
                  ·
                    refine ⟨11766607743631478024014085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31377620649683941397370893 11766607743631478024014085)
                    ·
                      refine ⟨2206238951930902129502641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11766607743631478024014085 2206238951930902129502641)
                      ·
                        rfl

theorem cell23_4296635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_4296635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296635 prefixEnd_4296635 := by exact prefixLift 4296635
  have htrace : WordTrace (prefixWord ++ tailWord_4296635) baseStart_4296635 baseEnd_4296635 := by
    simpa [prefixWord, tailWord_4296635, baseEnd_4296635] using wordTrace_append hprefix tailTrace_4296635
  have hstable : (prefixWord ++ tailWord_4296635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296635).length < 2 ^ (prefixWord ++ tailWord_4296635).sum := by decide
  have hdescent : baseEnd_4296635 < baseStart_4296635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296652 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4296652 : Nat := 118140960795 + 4296652 * 2 ^ 59
def prefixEnd_4296652 : Nat := 4983230072969 + 3 ^ 40 * 4296652 * 2
def baseEnd_4296652 : Nat := 2206247681102028562990063

theorem tailTrace_4296652 : CollatzResearch.WordTrace tailWord_4296652 prefixEnd_4296652 2206247681102028562990063 := by
  unfold tailWord_4296652
  simp only [CollatzResearch.WordTrace]
  refine ⟨78355886414985544292566105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104474515219980725723421473 78355886414985544292566105)
  ·
    refine ⟨58766914811239158219424579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78355886414985544292566105 58766914811239158219424579)
    ·
      refine ⟨88150372216858737329136869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58766914811239158219424579 88150372216858737329136869)
      ·
        refine ⟨16528194790661013249213163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88150372216858737329136869 16528194790661013249213163)
        ·
          refine ⟨24792292185991519873819745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16528194790661013249213163 24792292185991519873819745)
          ·
            refine ⟨18594219139493639905364809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24792292185991519873819745 18594219139493639905364809)
            ·
              refine ⟨13945664354620229929023607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18594219139493639905364809 13945664354620229929023607)
              ·
                refine ⟨20918496531930344893535411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13945664354620229929023607 20918496531930344893535411)
                ·
                  refine ⟨31377744797895517340303117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20918496531930344893535411 31377744797895517340303117)
                  ·
                    refine ⟨11766654299210819002613669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31377744797895517340303117 11766654299210819002613669)
                    ·
                      refine ⟨2206247681102028562990063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11766654299210819002613669 2206247681102028562990063)
                      ·
                        rfl

theorem cell23_4296652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4296652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296652 prefixEnd_4296652 := by exact prefixLift 4296652
  have htrace : WordTrace (prefixWord ++ tailWord_4296652) baseStart_4296652 baseEnd_4296652 := by
    simpa [prefixWord, tailWord_4296652, baseEnd_4296652] using wordTrace_append hprefix tailTrace_4296652
  have hstable : (prefixWord ++ tailWord_4296652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296652).length < 2 ^ (prefixWord ++ tailWord_4296652).sum := by decide
  have hdescent : baseEnd_4296652 < baseStart_4296652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296752 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_4296752 : Nat := 118140960795 + 4296752 * 2 ^ 59
def prefixEnd_4296752 : Nat := 4983230072969 + 3 ^ 40 * 4296752 * 2
def baseEnd_4296752 : Nat := 735433009722492723913201

theorem tailTrace_4296752 : CollatzResearch.WordTrace tailWord_4296752 prefixEnd_4296752 735433009722492723913201 := by
  unfold tailWord_4296752
  simp only [CollatzResearch.WordTrace]
  refine ⟨78357710064804402831886255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104476946753072537109181673 78357710064804402831886255)
  ·
    refine ⟨117536565097206604247829383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78357710064804402831886255 117536565097206604247829383)
    ·
      refine ⟨176304847645809906371744075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117536565097206604247829383 176304847645809906371744075)
      ·
        refine ⟨264457271468714859557616113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176304847645809906371744075 264457271468714859557616113)
        ·
          refine ⟨198342953601536144668212085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264457271468714859557616113 198342953601536144668212085)
          ·
            refine ⟨18594651900144013562644883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198342953601536144668212085 18594651900144013562644883)
            ·
              refine ⟨27891977850216020343967325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18594651900144013562644883 27891977850216020343967325)
              ·
                refine ⟨10459491693831007628987747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27891977850216020343967325 10459491693831007628987747)
                ·
                  refine ⟨15689237540746511443481621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10459491693831007628987747 15689237540746511443481621)
                  ·
                    refine ⟨735433009722492723913201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15689237540746511443481621 735433009722492723913201)
                    ·
                      rfl

theorem cell23_4296752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_4296752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296752 prefixEnd_4296752 := by exact prefixLift 4296752
  have htrace : WordTrace (prefixWord ++ tailWord_4296752) baseStart_4296752 baseEnd_4296752 := by
    simpa [prefixWord, tailWord_4296752, baseEnd_4296752] using wordTrace_append hprefix tailTrace_4296752
  have hstable : (prefixWord ++ tailWord_4296752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296752).length < 2 ^ (prefixWord ++ tailWord_4296752).sum := by decide
  have hdescent : baseEnd_4296752 < baseStart_4296752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296769 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4296769 : Nat := 118140960795 + 4296769 * 2 ^ 59
def prefixEnd_4296769 : Nat := 4983230072969 + 3 ^ 40 * 4296769 * 2
def baseEnd_4296769 : Nat := 735435919446201535075675

theorem tailTrace_4296769 : CollatzResearch.WordTrace tailWord_4296769 prefixEnd_4296769 735435919446201535075675 := by
  unfold tailWord_4296769
  simp only [CollatzResearch.WordTrace]
  refine ⟨156716040170547217567141361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104477360113698145044760907 156716040170547217567141361)
  ·
    refine ⟨117537030127910413175356021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156716040170547217567141361 117537030127910413175356021)
    ·
      refine ⟨11019096574491601235189627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117537030127910413175356021 11019096574491601235189627)
      ·
        refine ⟨16528644861737401852784441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11019096574491601235189627 16528644861737401852784441)
        ·
          refine ⟨12396483646303051389588331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16528644861737401852784441 12396483646303051389588331)
          ·
            refine ⟨18594725469454577084382497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12396483646303051389588331 18594725469454577084382497)
            ·
              refine ⟨13946044102090932813286873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18594725469454577084382497 13946044102090932813286873)
              ·
                refine ⟨10459533076568199609965155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13946044102090932813286873 10459533076568199609965155)
                ·
                  refine ⟨15689299614852299414947733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10459533076568199609965155 15689299614852299414947733)
                  ·
                    refine ⟨735435919446201535075675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15689299614852299414947733 735435919446201535075675)
                    ·
                      rfl

theorem cell23_4296769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4296769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296769 prefixEnd_4296769 := by exact prefixLift 4296769
  have htrace : WordTrace (prefixWord ++ tailWord_4296769) baseStart_4296769 baseEnd_4296769 := by
    simpa [prefixWord, tailWord_4296769, baseEnd_4296769] using wordTrace_append hprefix tailTrace_4296769
  have hstable : (prefixWord ++ tailWord_4296769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296769).length < 2 ^ (prefixWord ++ tailWord_4296769).sum := by decide
  have hdescent : baseEnd_4296769 < baseStart_4296769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296779 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 3]
def baseStart_4296779 : Nat := 118140960795 + 4296779 * 2 ^ 59
def prefixEnd_4296779 : Nat := 4983230072969 + 3 ^ 40 * 4296779 * 2
def baseEnd_4296779 : Nat := 2206312893145149566101979

theorem tailTrace_4296779 : CollatzResearch.WordTrace tailWord_4296779 prefixEnd_4296779 2206312893145149566101979 := by
  unfold tailWord_4296779
  simp only [CollatzResearch.WordTrace]
  refine ⟨156716404900510989275005391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104477603267007326183336927 156716404900510989275005391)
  ·
    refine ⟨235074607350766483912508087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156716404900510989275005391 235074607350766483912508087)
    ·
      refine ⟨352611911026149725868762131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235074607350766483912508087 352611911026149725868762131)
      ·
        refine ⟨528917866539224588803143197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352611911026149725868762131 528917866539224588803143197)
        ·
          refine ⟨198344199952209220801178699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528917866539224588803143197 198344199952209220801178699)
          ·
            refine ⟨297516299928313831201768049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198344199952209220801178699 297516299928313831201768049)
            ·
              refine ⟨223137224946235373401326037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297516299928313831201768049 223137224946235373401326037)
              ·
                refine ⟨5229778709677391564093579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 223137224946235373401326037 5229778709677391564093579)
                ·
                  refine ⟨7844668064516087346140369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5229778709677391564093579 7844668064516087346140369)
                  ·
                    refine ⟨5883501048387065509605277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7844668064516087346140369 5883501048387065509605277)
                    ·
                      refine ⟨2206312893145149566101979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5883501048387065509605277 2206312893145149566101979)
                      ·
                        rfl

theorem cell23_4296779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 3].length) (baseStart_4296779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296779 prefixEnd_4296779 := by exact prefixLift 4296779
  have htrace : WordTrace (prefixWord ++ tailWord_4296779) baseStart_4296779 baseEnd_4296779 := by
    simpa [prefixWord, tailWord_4296779, baseEnd_4296779] using wordTrace_append hprefix tailTrace_4296779
  have hstable : (prefixWord ++ tailWord_4296779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296779).length < 2 ^ (prefixWord ++ tailWord_4296779).sum := by decide
  have hdescent : baseEnd_4296779 < baseStart_4296779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296782 : List Nat := [4, 1, 1, 1, 1, 5, 10]
def baseStart_4296782 : Nat := 118140960795 + 4296782 * 2 ^ 59
def prefixEnd_4296782 : Nat := 4983230072969 + 3 ^ 40 * 4296782 * 2
def baseEnd_4296782 : Nat := 27238449797371766103265

theorem tailTrace_4296782 : CollatzResearch.WordTrace tailWord_4296782 prefixEnd_4296782 27238449797371766103265 := by
  unfold tailWord_4296782
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589564289937515098420575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104477676213000080524909733 19589564289937515098420575)
  ·
    refine ⟨29384346434906272647630863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19589564289937515098420575 29384346434906272647630863)
    ·
      refine ⟨44076519652359408971446295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29384346434906272647630863 44076519652359408971446295)
      ·
        refine ⟨66114779478539113457169443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44076519652359408971446295 66114779478539113457169443)
        ·
          refine ⟨99172169217808670185754165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66114779478539113457169443 99172169217808670185754165)
          ·
            refine ⟨9297390864169562829914453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99172169217808670185754165 9297390864169562829914453)
            ·
              refine ⟨27238449797371766103265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9297390864169562829914453 27238449797371766103265)
              ·
                rfl

theorem cell23_4296782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 10].length) (baseStart_4296782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296782 prefixEnd_4296782 := by exact prefixLift 4296782
  have htrace : WordTrace (prefixWord ++ tailWord_4296782) baseStart_4296782 baseEnd_4296782 := by
    simpa [prefixWord, tailWord_4296782, baseEnd_4296782] using wordTrace_append hprefix tailTrace_4296782
  have hstable : (prefixWord ++ tailWord_4296782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296782).length < 2 ^ (prefixWord ++ tailWord_4296782).sum := by decide
  have hdescent : baseEnd_4296782 < baseStart_4296782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296786 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_4296786 : Nat := 118140960795 + 4296786 * 2 ^ 59
def prefixEnd_4296786 : Nat := 4983230072969 + 3 ^ 40 * 4296786 * 2
def baseEnd_4296786 : Nat := 735438829169910346238149

theorem tailTrace_4296786 : CollatzResearch.WordTrace tailWord_4296786 prefixEnd_4296786 735438829169910346238149 := by
  unfold tailWord_4296786
  simp only [CollatzResearch.WordTrace]
  refine ⟨39179165052871407367627553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104477773474323752980340141 39179165052871407367627553)
  ·
    refine ⟨29384373789653555525720665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39179165052871407367627553 29384373789653555525720665)
    ·
      refine ⟨22038280342240166644290499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29384373789653555525720665 22038280342240166644290499)
      ·
        refine ⟨33057420513360249966435749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22038280342240166644290499 33057420513360249966435749)
        ·
          refine ⟨6198266346255046868706703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33057420513360249966435749 6198266346255046868706703)
          ·
            refine ⟨9297399519382570303060055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198266346255046868706703 9297399519382570303060055)
            ·
              refine ⟨13946099279073855454590083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9297399519382570303060055 13946099279073855454590083)
              ·
                refine ⟨20919148918610783181885125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13946099279073855454590083 20919148918610783181885125)
                ·
                  refine ⟨3922340422239521846603461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20919148918610783181885125 3922340422239521846603461)
                  ·
                    refine ⟨735438829169910346238149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3922340422239521846603461 735438829169910346238149)
                    ·
                      rfl

theorem cell23_4296786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_4296786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296786 prefixEnd_4296786 := by exact prefixLift 4296786
  have htrace : WordTrace (prefixWord ++ tailWord_4296786) baseStart_4296786 baseEnd_4296786 := by
    simpa [prefixWord, tailWord_4296786, baseEnd_4296786] using wordTrace_append hprefix tailTrace_4296786
  have hstable : (prefixWord ++ tailWord_4296786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296786).length < 2 ^ (prefixWord ++ tailWord_4296786).sum := by decide
  have hdescent : baseEnd_4296786 < baseStart_4296786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296793 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 1, 2, 2]
def baseStart_4296793 : Nat := 118140960795 + 4296793 * 2 ^ 59
def prefixEnd_4296793 : Nat := 4983230072969 + 3 ^ 40 * 4296793 * 2
def baseEnd_4296793 : Nat := 2206320081874312511326915

theorem tailTrace_4296793 : CollatzResearch.WordTrace tailWord_4296793 prefixEnd_4296793 2206320081874312511326915 := by
  unfold tailWord_4296793
  simp only [CollatzResearch.WordTrace]
  refine ⟨156716915522460269666015033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104477943681640179777343355 156716915522460269666015033)
  ·
    refine ⟨117537686641845202249511275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156716915522460269666015033 117537686641845202249511275)
    ·
      refine ⟨176306529962767803374266913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117537686641845202249511275 176306529962767803374266913)
      ·
        refine ⟨132229897472075852530700185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176306529962767803374266913 132229897472075852530700185)
        ·
          refine ⟨99172423104056889398025139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132229897472075852530700185 99172423104056889398025139)
          ·
            refine ⟨148758634656085334097037709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99172423104056889398025139 148758634656085334097037709)
            ·
              refine ⟨55784487996032000286389141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148758634656085334097037709 55784487996032000286389141)
              ·
                refine ⟨2614897874814000013424491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55784487996032000286389141 2614897874814000013424491)
                ·
                  refine ⟨3922346812221000020136737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614897874814000013424491 3922346812221000020136737)
                  ·
                    refine ⟨2941760109165750015102553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3922346812221000020136737 2941760109165750015102553)
                    ·
                      refine ⟨2206320081874312511326915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941760109165750015102553 2206320081874312511326915)
                      ·
                        rfl

theorem cell23_4296793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_4296793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296793 prefixEnd_4296793 := by exact prefixLift 4296793
  have htrace : WordTrace (prefixWord ++ tailWord_4296793) baseStart_4296793 baseEnd_4296793 := by
    simpa [prefixWord, tailWord_4296793, baseEnd_4296793] using wordTrace_append hprefix tailTrace_4296793
  have hstable : (prefixWord ++ tailWord_4296793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296793).length < 2 ^ (prefixWord ++ tailWord_4296793).sum := by decide
  have hdescent : baseEnd_4296793 < baseStart_4296793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296832 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_4296832 : Nat := 118140960795 + 4296832 * 2 ^ 59
def prefixEnd_4296832 : Nat := 4983230072969 + 3 ^ 40 * 4296832 * 2
def baseEnd_4296832 : Nat := 2206340107619837858739235

theorem tailTrace_4296832 : CollatzResearch.WordTrace tailWord_4296832 prefixEnd_4296832 2206340107619837858739235 := by
  unfold tailWord_4296832
  simp only [CollatzResearch.WordTrace]
  refine ⟨78359168984659489663342375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104478891979545986217789833 78359168984659489663342375)
  ·
    refine ⟨117538753476989234495013563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78359168984659489663342375 117538753476989234495013563)
    ·
      refine ⟨176308130215483851742520345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117538753476989234495013563 176308130215483851742520345)
      ·
        refine ⟨132231097661612888806890259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176308130215483851742520345 132231097661612888806890259)
        ·
          refine ⟨198346646492419333210335389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132231097661612888806890259 198346646492419333210335389)
          ·
            refine ⟨74379992434657249953875771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198346646492419333210335389 74379992434657249953875771)
            ·
              refine ⟨111569988651985874930813657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74379992434657249953875771 111569988651985874930813657)
              ·
                refine ⟨83677491488989406198110243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111569988651985874930813657 83677491488989406198110243)
                ·
                  refine ⟨125516237233484109297165365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83677491488989406198110243 125516237233484109297165365)
                  ·
                    refine ⟨11767147240639135246609253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125516237233484109297165365 11767147240639135246609253)
                    ·
                      refine ⟨2206340107619837858739235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11767147240639135246609253 2206340107619837858739235)
                      ·
                        rfl

theorem cell23_4296832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_4296832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296832 prefixEnd_4296832 := by exact prefixLift 4296832
  have htrace : WordTrace (prefixWord ++ tailWord_4296832) baseStart_4296832 baseEnd_4296832 := by
    simpa [prefixWord, tailWord_4296832, baseEnd_4296832] using wordTrace_append hprefix tailTrace_4296832
  have hstable : (prefixWord ++ tailWord_4296832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296832).length < 2 ^ (prefixWord ++ tailWord_4296832).sum := by decide
  have hdescent : baseEnd_4296832 < baseStart_4296832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296854 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4296854 : Nat := 118140960795 + 4296854 * 2 ^ 59
def prefixEnd_4296854 : Nat := 4983230072969 + 3 ^ 40 * 4296854 * 2
def baseEnd_4296854 : Nat := 735450468064745590888045

theorem tailTrace_4296854 : CollatzResearch.WordTrace tailWord_4296854 prefixEnd_4296854 735450468064745590888045 := by
  unfold tailWord_4296854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794946273452454817749101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104479426916826184722657077 9794946273452454817749101)
  ·
    refine ⟨3673104852544670556655913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9794946273452454817749101 3673104852544670556655913)
    ·
      refine ⟨2754828639408502917491935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3673104852544670556655913 2754828639408502917491935)
      ·
        refine ⟨4132242959112754376237903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754828639408502917491935 4132242959112754376237903)
        ·
          refine ⟨6198364438669131564356855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132242959112754376237903 6198364438669131564356855)
          ·
            refine ⟨9297546658003697346535283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198364438669131564356855 9297546658003697346535283)
            ·
              refine ⟨13946319987005546019802925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9297546658003697346535283 13946319987005546019802925)
              ·
                refine ⟨5229869995127079757426097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13946319987005546019802925 5229869995127079757426097)
                ·
                  refine ⟨3922402496345309818069573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5229869995127079757426097 3922402496345309818069573)
                  ·
                    refine ⟨735450468064745590888045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3922402496345309818069573 735450468064745590888045)
                    ·
                      rfl

theorem cell23_4296854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4296854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296854 prefixEnd_4296854 := by exact prefixLift 4296854
  have htrace : WordTrace (prefixWord ++ tailWord_4296854) baseStart_4296854 baseEnd_4296854 := by
    simpa [prefixWord, tailWord_4296854, baseEnd_4296854] using wordTrace_append hprefix tailTrace_4296854
  have hstable : (prefixWord ++ tailWord_4296854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296854).length < 2 ^ (prefixWord ++ tailWord_4296854).sum := by decide
  have hdescent : baseEnd_4296854 < baseStart_4296854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296900 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_4296900 : Nat := 118140960795 + 4296900 * 2 ^ 59
def prefixEnd_4296900 : Nat := 4983230072969 + 3 ^ 40 * 4296900 * 2
def baseEnd_4296900 : Nat := 2206375024304343592688923

theorem tailTrace_4296900 : CollatzResearch.WordTrace tailWord_4296900 prefixEnd_4296900 2206375024304343592688923 := by
  unfold tailWord_4296900
  simp only [CollatzResearch.WordTrace]
  refine ⟨78360409066536313470080077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104480545422048417960106769 78360409066536313470080077)
  ·
    refine ⟨29385153399951117551280029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78360409066536313470080077 29385153399951117551280029)
    ·
      refine ⟨11019432524981669081730011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29385153399951117551280029 11019432524981669081730011)
      ·
        refine ⟨16529148787472503622595017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11019432524981669081730011 16529148787472503622595017)
        ·
          refine ⟨12396861590604377716946263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16529148787472503622595017 12396861590604377716946263)
          ·
            refine ⟨18595292385906566575419395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12396861590604377716946263 18595292385906566575419395)
            ·
              refine ⟨27892938578859849863129093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18595292385906566575419395 27892938578859849863129093)
              ·
                refine ⟨5229925983536221849336705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27892938578859849863129093 5229925983536221849336705)
                ·
                  refine ⟨3922444487652166387002529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5229925983536221849336705 3922444487652166387002529)
                  ·
                    refine ⟨2941833365739124790251897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3922444487652166387002529 2941833365739124790251897)
                    ·
                      refine ⟨2206375024304343592688923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941833365739124790251897 2206375024304343592688923)
                      ·
                        rfl

theorem cell23_4296900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_4296900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296900 prefixEnd_4296900 := by exact prefixLift 4296900
  have htrace : WordTrace (prefixWord ++ tailWord_4296900) baseStart_4296900 baseEnd_4296900 := by
    simpa [prefixWord, tailWord_4296900, baseEnd_4296900] using wordTrace_append hprefix tailTrace_4296900
  have hstable : (prefixWord ++ tailWord_4296900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296900).length < 2 ^ (prefixWord ++ tailWord_4296900).sum := by decide
  have hdescent : baseEnd_4296900 < baseStart_4296900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296906 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_4296906 : Nat := 118140960795 + 4296906 * 2 ^ 59
def prefixEnd_4296906 : Nat := 4983230072969 + 3 ^ 40 * 4296906 * 2
def baseEnd_4296906 : Nat := 245153122798696729912655

theorem tailTrace_4296906 : CollatzResearch.WordTrace tailWord_4296906 prefixEnd_4296906 245153122798696729912655 := by
  unfold tailWord_4296906
  simp only [CollatzResearch.WordTrace]
  refine ⟨39180259242762722491219643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104480691314033926643252381 39180259242762722491219643)
  ·
    refine ⟨58770388864144083736829465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39180259242762722491219643 58770388864144083736829465)
    ·
      refine ⟨44077791648108062802622099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58770388864144083736829465 44077791648108062802622099)
      ·
        refine ⟨66116687472162094203933149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44077791648108062802622099 66116687472162094203933149)
        ·
          refine ⟨24793757802060785326474931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66116687472162094203933149 24793757802060785326474931)
          ·
            refine ⟨37190636703091177989712397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24793757802060785326474931 37190636703091177989712397)
            ·
              refine ⟨13946488763659191746142149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37190636703091177989712397 13946488763659191746142149)
              ·
                refine ⟨2614966643186098452401653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13946488763659191746142149 2614966643186098452401653)
                ·
                  refine ⟨245153122798696729912655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2614966643186098452401653 245153122798696729912655)
                  ·
                    rfl

theorem cell23_4296906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_4296906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296906 prefixEnd_4296906 := by exact prefixLift 4296906
  have htrace : WordTrace (prefixWord ++ tailWord_4296906) baseStart_4296906 baseEnd_4296906 := by
    simpa [prefixWord, tailWord_4296906, baseEnd_4296906] using wordTrace_append hprefix tailTrace_4296906
  have hstable : (prefixWord ++ tailWord_4296906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296906).length < 2 ^ (prefixWord ++ tailWord_4296906).sum := by decide
  have hdescent : baseEnd_4296906 < baseStart_4296906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296936 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 2, 5]
def baseStart_4296936 : Nat := 118140960795 + 4296936 * 2 ^ 59
def prefixEnd_4296936 : Nat := 4983230072969 + 3 ^ 40 * 4296936 * 2
def baseEnd_4296936 : Nat := 735464503202635150612919

theorem tailTrace_4296936 : CollatzResearch.WordTrace tailWord_4296936 prefixEnd_4296936 735464503202635150612919 := by
  unfold tailWord_4296936
  simp only [CollatzResearch.WordTrace]
  refine ⟨78361065580471102544235331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104481420773961470058980441 78361065580471102544235331)
  ·
    refine ⟨117541598370706653816352997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78361065580471102544235331 117541598370706653816352997)
    ·
      refine ⟨22039049694507497590566187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117541598370706653816352997 22039049694507497590566187)
      ·
        refine ⟨33058574541761246385849281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22039049694507497590566187 33058574541761246385849281)
        ·
          refine ⟨24793930906320934789386961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33058574541761246385849281 24793930906320934789386961)
          ·
            refine ⟨18595448179740701092040221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24793930906320934789386961 18595448179740701092040221)
            ·
              refine ⟨6973293067402762909515083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18595448179740701092040221 6973293067402762909515083)
              ·
                refine ⟨10459939601104144364272625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973293067402762909515083 10459939601104144364272625)
                ·
                  refine ⟨7844954700828108273204469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10459939601104144364272625 7844954700828108273204469)
                  ·
                    refine ⟨735464503202635150612919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7844954700828108273204469 735464503202635150612919)
                    ·
                      rfl

theorem cell23_4296936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_4296936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296936 prefixEnd_4296936 := by exact prefixLift 4296936
  have htrace : WordTrace (prefixWord ++ tailWord_4296936) baseStart_4296936 baseEnd_4296936 := by
    simpa [prefixWord, tailWord_4296936, baseEnd_4296936] using wordTrace_append hprefix tailTrace_4296936
  have hstable : (prefixWord ++ tailWord_4296936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296936).length < 2 ^ (prefixWord ++ tailWord_4296936).sum := by decide
  have hdescent : baseEnd_4296936 < baseStart_4296936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296939 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4]
def baseStart_4296939 : Nat := 118140960795 + 4296939 * 2 ^ 59
def prefixEnd_4296939 : Nat := 4983230072969 + 3 ^ 40 * 4296939 * 2
def baseEnd_4296939 : Nat := 2206395050049868940101243

theorem tailTrace_4296939 : CollatzResearch.WordTrace tailWord_4296939 prefixEnd_4296939 2206395050049868940101243 := by
  unfold tailWord_4296939
  simp only [CollatzResearch.WordTrace]
  refine ⟨156722240579931336600829871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104481493719954224400553247 156722240579931336600829871)
  ·
    refine ⟨235083360869897004901244807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156722240579931336600829871 235083360869897004901244807)
    ·
      refine ⟨352625041304845507351867211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235083360869897004901244807 352625041304845507351867211)
      ·
        refine ⟨528937561957268261027800817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352625041304845507351867211 528937561957268261027800817)
        ·
          refine ⟨396703171467951195770850613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528937561957268261027800817 396703171467951195770850613)
          ·
            refine ⟨37190922325120424603517245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 396703171467951195770850613 37190922325120424603517245)
            ·
              refine ⟨13946595871920159226318967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37190922325120424603517245 13946595871920159226318967)
              ·
                refine ⟨20919893807880238839478451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13946595871920159226318967 20919893807880238839478451)
                ·
                  refine ⟨31379840711820358259217677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20919893807880238839478451 31379840711820358259217677)
                  ·
                    refine ⟨11767440266932634347206629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31379840711820358259217677 11767440266932634347206629)
                    ·
                      refine ⟨2206395050049868940101243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11767440266932634347206629 2206395050049868940101243)
                      ·
                        rfl

theorem cell23_4296939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_4296939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296939 prefixEnd_4296939 := by exact prefixLift 4296939
  have htrace : WordTrace (prefixWord ++ tailWord_4296939) baseStart_4296939 baseEnd_4296939 := by
    simpa [prefixWord, tailWord_4296939, baseEnd_4296939] using wordTrace_append hprefix tailTrace_4296939
  have hstable : (prefixWord ++ tailWord_4296939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296939).length < 2 ^ (prefixWord ++ tailWord_4296939).sum := by decide
  have hdescent : baseEnd_4296939 < baseStart_4296939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4296979 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 6]
def baseStart_4296979 : Nat := 118140960795 + 4296979 * 2 ^ 59
def prefixEnd_4296979 : Nat := 4983230072969 + 3 ^ 40 * 4296979 * 2
def baseEnd_4296979 : Nat := 245157287697338753733451

theorem tailTrace_4296979 : CollatzResearch.WordTrace tailWord_4296979 prefixEnd_4296979 245157287697338753733451 := by
  unfold tailWord_4296979
  simp only [CollatzResearch.WordTrace]
  refine ⟨156723699499786423432285991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104482466333190948954857327 156723699499786423432285991)
  ·
    refine ⟨235085549249679635148428987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156723699499786423432285991 235085549249679635148428987)
    ·
      refine ⟨352628323874519452722643481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235085549249679635148428987 352628323874519452722643481)
      ·
        refine ⟨264471242905889589541982611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352628323874519452722643481 264471242905889589541982611)
        ·
          refine ⟨396706864358834384312973917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264471242905889589541982611 396706864358834384312973917)
          ·
            refine ⟨148765074134562894117365219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396706864358834384312973917 148765074134562894117365219)
            ·
              refine ⟨223147611201844341176047829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148765074134562894117365219 223147611201844341176047829)
              ·
                refine ⟨5230022137543226746313621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 223147611201844341176047829 5230022137543226746313621)
                ·
                  refine ⟨245157287697338753733451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5230022137543226746313621 245157287697338753733451)
                  ·
                    rfl

theorem cell23_4296979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 6].length) (baseStart_4296979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4296979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4296979 prefixEnd_4296979 := by exact prefixLift 4296979
  have htrace : WordTrace (prefixWord ++ tailWord_4296979) baseStart_4296979 baseEnd_4296979 := by
    simpa [prefixWord, tailWord_4296979, baseEnd_4296979] using wordTrace_append hprefix tailTrace_4296979
  have hstable : (prefixWord ++ tailWord_4296979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4296979).length < 2 ^ (prefixWord ++ tailWord_4296979).sum := by decide
  have hdescent : baseEnd_4296979 < baseStart_4296979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4296979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297017 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 1, 4]
def baseStart_4297017 : Nat := 118140960795 + 4297017 * 2 ^ 59
def prefixEnd_4297017 : Nat := 4983230072969 + 3 ^ 40 * 4297017 * 2
def baseEnd_4297017 : Nat := 735478367180306544975295

theorem tailTrace_4297017 : CollatzResearch.WordTrace tailWord_4297017 prefixEnd_4297017 735478367180306544975295 := by
  unfold tailWord_4297017
  simp only [CollatzResearch.WordTrace]
  refine ⟨156725085473648755922169305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104483390315765837281446203 156725085473648755922169305)
  ·
    refine ⟨117543814105236566941626979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156725085473648755922169305 117543814105236566941626979)
    ·
      refine ⟨176315721157854850412440469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117543814105236566941626979 176315721157854850412440469)
      ·
        refine ⟨8264799429274446113083147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 176315721157854850412440469 8264799429274446113083147)
        ·
          refine ⟨12397199143911669169624721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8264799429274446113083147 12397199143911669169624721)
          ·
            refine ⟨9297899357933751877218541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12397199143911669169624721 9297899357933751877218541)
            ·
              refine ⟨3486712259225156953956953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9297899357933751877218541 3486712259225156953956953)
              ·
                refine ⟨2615034194418867715467715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486712259225156953956953 2615034194418867715467715)
                ·
                  refine ⟨3922551291628301573201573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615034194418867715467715 3922551291628301573201573)
                  ·
                    refine ⟨735478367180306544975295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3922551291628301573201573 735478367180306544975295)
                    ·
                      rfl

theorem cell23_4297017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 4].length) (baseStart_4297017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297017 prefixEnd_4297017 := by exact prefixLift 4297017
  have htrace : WordTrace (prefixWord ++ tailWord_4297017) baseStart_4297017 baseEnd_4297017 := by
    simpa [prefixWord, tailWord_4297017, baseEnd_4297017] using wordTrace_append hprefix tailTrace_4297017
  have hstable : (prefixWord ++ tailWord_4297017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297017).length < 2 ^ (prefixWord ++ tailWord_4297017).sum := by decide
  have hdescent : baseEnd_4297017 < baseStart_4297017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297029 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_4297029 : Nat := 118140960795 + 4297029 * 2 ^ 59
def prefixEnd_4297029 : Nat := 4983230072969 + 3 ^ 40 * 4297029 * 2
def baseEnd_4297029 : Nat := 2206441263308773587975829

theorem tailTrace_4297029 : CollatzResearch.WordTrace tailWord_4297029 prefixEnd_4297029 2206441263308773587975829 := by
  unfold tailWord_4297029
  simp only [CollatzResearch.WordTrace]
  refine ⟨156725523149605281971606141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104483682099736854647737427 156725523149605281971606141)
  ·
    refine ⟨58772071181101980739352303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156725523149605281971606141 58772071181101980739352303)
    ·
      refine ⟨88158106771652971109028455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58772071181101980739352303 88158106771652971109028455)
      ·
        refine ⟨132237160157479456663542683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88158106771652971109028455 132237160157479456663542683)
        ·
          refine ⟨198355740236219184995314025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132237160157479456663542683 198355740236219184995314025)
          ·
            refine ⟨148766805177164388746485519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198355740236219184995314025 148766805177164388746485519)
            ·
              refine ⟨223150207765746583119728279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148766805177164388746485519 223150207765746583119728279)
              ·
                refine ⟨334725311648619874679592419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223150207765746583119728279 334725311648619874679592419)
                ·
                  refine ⟨502087967472929812019388629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334725311648619874679592419 502087967472929812019388629)
                  ·
                    refine ⟨11767686737646792469204421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 502087967472929812019388629 11767686737646792469204421)
                    ·
                      refine ⟨2206441263308773587975829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11767686737646792469204421 2206441263308773587975829)
                      ·
                        rfl

theorem cell23_4297029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_4297029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297029 prefixEnd_4297029 := by exact prefixLift 4297029
  have htrace : WordTrace (prefixWord ++ tailWord_4297029) baseStart_4297029 baseEnd_4297029 := by
    simpa [prefixWord, tailWord_4297029, baseEnd_4297029] using wordTrace_append hprefix tailTrace_4297029
  have hstable : (prefixWord ++ tailWord_4297029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297029).length < 2 ^ (prefixWord ++ tailWord_4297029).sum := by decide
  have hdescent : baseEnd_4297029 < baseStart_4297029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297074 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_4297074 : Nat := 118140960795 + 4297074 * 2 ^ 59
def prefixEnd_4297074 : Nat := 4983230072969 + 3 ^ 40 * 4297074 * 2
def baseEnd_4297074 : Nat := 2206464369938225911913123

theorem tailTrace_4297074 : CollatzResearch.WordTrace tailWord_4297074 prefixEnd_4297074 2206464369938225911913123 := by
  unfold tailWord_4297074
  simp only [CollatzResearch.WordTrace]
  refine ⟨39181791108610563664248569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104484776289628169771329517 39181791108610563664248569)
  ·
    refine ⟨29386343331457922748186427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39181791108610563664248569 29386343331457922748186427)
    ·
      refine ⟨44079514997186884122279641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29386343331457922748186427 44079514997186884122279641)
      ·
        refine ⟨33059636247890163091709731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44079514997186884122279641 33059636247890163091709731)
        ·
          refine ⟨49589454371835244637564597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33059636247890163091709731 49589454371835244637564597)
          ·
            refine ⟨4649011347359554184771681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49589454371835244637564597 4649011347359554184771681)
            ·
              refine ⟨3486758510519665638578761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649011347359554184771681 3486758510519665638578761)
              ·
                refine ⟨2615068882889749228934071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486758510519665638578761 2615068882889749228934071)
                ·
                  refine ⟨3922603324334623843401107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615068882889749228934071 3922603324334623843401107)
                  ·
                    refine ⟨5883904986501935765101661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3922603324334623843401107 5883904986501935765101661)
                    ·
                      refine ⟨2206464369938225911913123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5883904986501935765101661 2206464369938225911913123)
                      ·
                        rfl

theorem cell23_4297074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_4297074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297074 prefixEnd_4297074 := by exact prefixLift 4297074
  have htrace : WordTrace (prefixWord ++ tailWord_4297074) baseStart_4297074 baseEnd_4297074 := by
    simpa [prefixWord, tailWord_4297074, baseEnd_4297074] using wordTrace_append hprefix tailTrace_4297074
  have hstable : (prefixWord ++ tailWord_4297074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297074).length < 2 ^ (prefixWord ++ tailWord_4297074).sum := by decide
  have hdescent : baseEnd_4297074 < baseStart_4297074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297079 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_4297079 : Nat := 118140960795 + 4297079 * 2 ^ 59
def prefixEnd_4297079 : Nat := 4983230072969 + 3 ^ 40 * 4297079 * 2
def baseEnd_4297079 : Nat := 2206466937341498392350599

theorem tailTrace_4297079 : CollatzResearch.WordTrace tailWord_4297079 prefixEnd_4297079 2206466937341498392350599 := by
  unfold tailWord_4297079
  simp only [CollatzResearch.WordTrace]
  refine ⟨156727346799424140510926291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104484897866282760340617527 156727346799424140510926291)
  ·
    refine ⟨235091020199136210766389437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156727346799424140510926291 235091020199136210766389437)
    ·
      refine ⟨88159132574676079037396039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235091020199136210766389437 88159132574676079037396039)
      ·
        refine ⟨132238698862014118556094059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88159132574676079037396039 132238698862014118556094059)
        ·
          refine ⟨198358048293021177834141089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132238698862014118556094059 198358048293021177834141089)
          ·
            refine ⟨148768536219765883375605817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198358048293021177834141089 148768536219765883375605817)
            ·
              refine ⟨111576402164824412531704363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148768536219765883375605817 111576402164824412531704363)
              ·
                refine ⟨167364603247236618797556545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111576402164824412531704363 167364603247236618797556545)
                ·
                  refine ⟨125523452435427464098167409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167364603247236618797556545 125523452435427464098167409)
                  ·
                    refine ⟨94142589326570598073625557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125523452435427464098167409 94142589326570598073625557)
                    ·
                      refine ⟨2206466937341498392350599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94142589326570598073625557 2206466937341498392350599)
                      ·
                        rfl

theorem cell23_4297079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_4297079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297079 prefixEnd_4297079 := by exact prefixLift 4297079
  have htrace : WordTrace (prefixWord ++ tailWord_4297079) baseStart_4297079 baseEnd_4297079 := by
    simpa [prefixWord, tailWord_4297079, baseEnd_4297079] using wordTrace_append hprefix tailTrace_4297079
  have hstable : (prefixWord ++ tailWord_4297079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297079).length < 2 ^ (prefixWord ++ tailWord_4297079).sum := by decide
  have hdescent : baseEnd_4297079 < baseStart_4297079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297113 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 3]
def baseStart_4297113 : Nat := 118140960795 + 4297113 * 2 ^ 59
def prefixEnd_4297113 : Nat := 4983230072969 + 3 ^ 40 * 4297113 * 2
def baseEnd_4297113 : Nat := 2206484395683751259325443

theorem tailTrace_4297113 : CollatzResearch.WordTrace tailWord_4297113 prefixEnd_4297113 2206484395683751259325443 := by
  unfold tailWord_4297113
  simp only [CollatzResearch.WordTrace]
  refine ⟨156728586881300964317663993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104485724587533976211775995 156728586881300964317663993)
  ·
    refine ⟨117546440160975723238247995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156728586881300964317663993 117546440160975723238247995)
    ·
      refine ⟨176319660241463584857371993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117546440160975723238247995 176319660241463584857371993)
      ·
        refine ⟨132239745181097688643028995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176319660241463584857371993 132239745181097688643028995)
        ·
          refine ⟨198359617771646532964543493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132239745181097688643028995 198359617771646532964543493)
          ·
            refine ⟨37192428332183724930851905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198359617771646532964543493 37192428332183724930851905)
            ·
              refine ⟨27894321249137793698138929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37192428332183724930851905 27894321249137793698138929)
              ·
                refine ⟨20920740936853345273604197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27894321249137793698138929 20920740936853345273604197)
                ·
                  refine ⟨3922638925660002238800787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20920740936853345273604197 3922638925660002238800787)
                  ·
                    refine ⟨5883958388490003358201181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3922638925660002238800787 5883958388490003358201181)
                    ·
                      refine ⟨2206484395683751259325443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5883958388490003358201181 2206484395683751259325443)
                      ·
                        rfl

theorem cell23_4297113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_4297113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297113 prefixEnd_4297113 := by exact prefixLift 4297113
  have htrace : WordTrace (prefixWord ++ tailWord_4297113) baseStart_4297113 baseEnd_4297113 := by
    simpa [prefixWord, tailWord_4297113, baseEnd_4297113] using wordTrace_append hprefix tailTrace_4297113
  have hstable : (prefixWord ++ tailWord_4297113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297113).length < 2 ^ (prefixWord ++ tailWord_4297113).sum := by decide
  have hdescent : baseEnd_4297113 < baseStart_4297113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297114 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2]
def baseStart_4297114 : Nat := 118140960795 + 4297114 * 2 ^ 59
def prefixEnd_4297114 : Nat := 4983230072969 + 3 ^ 40 * 4297114 * 2
def baseEnd_4297114 : Nat := 2206484909164405755412939

theorem tailTrace_4297114 : CollatzResearch.WordTrace tailWord_4297114 prefixEnd_4297114 2206484909164405755412939 := by
  unfold tailWord_4297114
  simp only [CollatzResearch.WordTrace]
  refine ⟨39182155838574335372112599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104485748902864894325633597 39182155838574335372112599)
  ·
    refine ⟨58773233757861503058168899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39182155838574335372112599 58773233757861503058168899)
    ·
      refine ⟨88159850636792254587253349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58773233757861503058168899 88159850636792254587253349)
      ·
        refine ⟨16529971994398547735110003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88159850636792254587253349 16529971994398547735110003)
        ·
          refine ⟨24794957991597821602665005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16529971994398547735110003 24794957991597821602665005)
          ·
            refine ⟨9298109246849183100999377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24794957991597821602665005 9298109246849183100999377)
            ·
              refine ⟨6973581935136887325749533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9298109246849183100999377 6973581935136887325749533)
              ·
                refine ⟨2615093225676332747156075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6973581935136887325749533 2615093225676332747156075)
                ·
                  refine ⟨3922639838514499120734113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615093225676332747156075 3922639838514499120734113)
                  ·
                    refine ⟨2941979878885874340550585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3922639838514499120734113 2941979878885874340550585)
                    ·
                      refine ⟨2206484909164405755412939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2941979878885874340550585 2206484909164405755412939)
                      ·
                        rfl

theorem cell23_4297114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_4297114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297114 prefixEnd_4297114 := by exact prefixLift 4297114
  have htrace : WordTrace (prefixWord ++ tailWord_4297114) baseStart_4297114 baseEnd_4297114 := by
    simpa [prefixWord, tailWord_4297114, baseEnd_4297114] using wordTrace_append hprefix tailTrace_4297114
  have hstable : (prefixWord ++ tailWord_4297114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297114).length < 2 ^ (prefixWord ++ tailWord_4297114).sum := by decide
  have hdescent : baseEnd_4297114 < baseStart_4297114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297173 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4297173 : Nat := 118140960795 + 4297173 * 2 ^ 59
def prefixEnd_4297173 : Nat := 4983230072969 + 3 ^ 40 * 4297173 * 2
def baseEnd_4297173 : Nat := 2206515204523021024575167

theorem tailTrace_4297173 : CollatzResearch.WordTrace tailWord_4297173 prefixEnd_4297173 2206515204523021024575167 := by
  unfold tailWord_4297173
  simp only [CollatzResearch.WordTrace]
  refine ⟨156730775261083594564848173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104487183507389063043232115 156730775261083594564848173)
  ·
    refine ⟨58774040722906347961818065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156730775261083594564848173 58774040722906347961818065)
    ·
      refine ⟨44080530542179760971363549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58774040722906347961818065 44080530542179760971363549)
      ·
        refine ⟨16530198953317410364261331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44080530542179760971363549 16530198953317410364261331)
        ·
          refine ⟨24795298429976115546391997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16530198953317410364261331 24795298429976115546391997)
          ·
            refine ⟨9298236911241043329896999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24795298429976115546391997 9298236911241043329896999)
            ·
              refine ⟨13947355366861564994845499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9298236911241043329896999 13947355366861564994845499)
              ·
                refine ⟨20921033050292347492268249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13947355366861564994845499 20921033050292347492268249)
                ·
                  refine ⟨15690774787719260619201187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20921033050292347492268249 15690774787719260619201187)
                  ·
                    refine ⟨23536162181578890928801781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15690774787719260619201187 23536162181578890928801781)
                    ·
                      refine ⟨2206515204523021024575167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23536162181578890928801781 2206515204523021024575167)
                      ·
                        rfl

theorem cell23_4297173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4297173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297173 prefixEnd_4297173 := by exact prefixLift 4297173
  have htrace : WordTrace (prefixWord ++ tailWord_4297173) baseStart_4297173 baseEnd_4297173 := by
    simpa [prefixWord, tailWord_4297173, baseEnd_4297173] using wordTrace_append hprefix tailTrace_4297173
  have hstable : (prefixWord ++ tailWord_4297173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297173).length < 2 ^ (prefixWord ++ tailWord_4297173).sum := by decide
  have hdescent : baseEnd_4297173 < baseStart_4297173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297243 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 6, 2]
def baseStart_4297243 : Nat := 118140960795 + 4297243 * 2 ^ 59
def prefixEnd_4297243 : Nat := 4983230072969 + 3 ^ 40 * 4297243 * 2
def baseEnd_4297243 : Nat := 2206551148168835750699845

theorem tailTrace_4297243 : CollatzResearch.WordTrace tailWord_4297243 prefixEnd_4297243 2206551148168835750699845 := by
  unfold tailWord_4297243
  simp only [CollatzResearch.WordTrace]
  refine ⟨156733328370829996519896383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104488885580553331013264255 156733328370829996519896383)
  ·
    refine ⟨235099992556244994779844575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156733328370829996519896383 235099992556244994779844575)
    ·
      refine ⟨352649988834367492169766863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235099992556244994779844575 352649988834367492169766863)
      ·
        refine ⟨528974983251551238254650295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352649988834367492169766863 528974983251551238254650295)
        ·
          refine ⟨793462474877326857381975443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528974983251551238254650295 793462474877326857381975443)
          ·
            refine ⟨1190193712315990286072963165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793462474877326857381975443 1190193712315990286072963165)
            ·
              refine ⟨446322642118496357277361187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190193712315990286072963165 446322642118496357277361187)
              ·
                refine ⟨669483963177744535916041781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446322642118496357277361187 669483963177744535916041781)
                ·
                  refine ⟨62764121547913550242128917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 669483963177744535916041781 62764121547913550242128917)
                  ·
                    refine ⟨2942068197558447667599793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62764121547913550242128917 2942068197558447667599793)
                    ·
                      refine ⟨2206551148168835750699845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942068197558447667599793 2206551148168835750699845)
                      ·
                        rfl

theorem cell23_4297243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6, 2].length) (baseStart_4297243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297243 prefixEnd_4297243 := by exact prefixLift 4297243
  have htrace : WordTrace (prefixWord ++ tailWord_4297243) baseStart_4297243 baseEnd_4297243 := by
    simpa [prefixWord, tailWord_4297243, baseEnd_4297243] using wordTrace_append hprefix tailTrace_4297243
  have hstable : (prefixWord ++ tailWord_4297243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297243).length < 2 ^ (prefixWord ++ tailWord_4297243).sum := by decide
  have hdescent : baseEnd_4297243 < baseStart_4297243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297277 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_4297277 : Nat := 118140960795 + 4297277 * 2 ^ 59
def prefixEnd_4297277 : Nat := 4983230072969 + 3 ^ 40 * 4297277 * 2
def baseEnd_4297277 : Nat := 2206568606511088617674689

theorem tailTrace_4297277 : CollatzResearch.WordTrace tailWord_4297277 prefixEnd_4297277 2206568606511088617674689 := by
  unfold tailWord_4297277
  simp only [CollatzResearch.WordTrace]
  refine ⟨156734568452706820326634085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104489712301804546884422723 156734568452706820326634085)
  ·
    refine ⟨29387731584882528811243891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156734568452706820326634085 29387731584882528811243891)
    ·
      refine ⟨44081597377323793216865837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29387731584882528811243891 44081597377323793216865837)
      ·
        refine ⟨16530599016496422456324689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44081597377323793216865837 16530599016496422456324689)
        ·
          refine ⟨12397949262372316842243517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16530599016496422456324689 12397949262372316842243517)
          ·
            refine ⟨4649230973389618815841319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12397949262372316842243517 4649230973389618815841319)
            ·
              refine ⟨6973846460084428223761979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649230973389618815841319 6973846460084428223761979)
              ·
                refine ⟨10460769690126642335642969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973846460084428223761979 10460769690126642335642969)
                ·
                  refine ⟨7845577267594981751732227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10460769690126642335642969 7845577267594981751732227)
                  ·
                    refine ⟨11768365901392472627598341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7845577267594981751732227 11768365901392472627598341)
                    ·
                      refine ⟨2206568606511088617674689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11768365901392472627598341 2206568606511088617674689)
                      ·
                        rfl

theorem cell23_4297277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_4297277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297277 prefixEnd_4297277 := by exact prefixLift 4297277
  have htrace : WordTrace (prefixWord ++ tailWord_4297277) baseStart_4297277 baseEnd_4297277 := by
    simpa [prefixWord, tailWord_4297277, baseEnd_4297277] using wordTrace_append hprefix tailTrace_4297277
  have hstable : (prefixWord ++ tailWord_4297277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297277).length < 2 ^ (prefixWord ++ tailWord_4297277).sum := by decide
  have hdescent : baseEnd_4297277 < baseStart_4297277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297280 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_4297280 : Nat := 118140960795 + 4297280 * 2 ^ 59
def prefixEnd_4297280 : Nat := 4983230072969 + 3 ^ 40 * 4297280 * 2
def baseEnd_4297280 : Nat := 2206570146953052105937175

theorem tailTrace_4297280 : CollatzResearch.WordTrace tailWord_4297280 prefixEnd_4297280 2206570146953052105937175 := by
  unfold tailWord_4297280
  simp only [CollatzResearch.WordTrace]
  refine ⟨78367338935847975919496647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104489785247797301225995529 78367338935847975919496647)
  ·
    refine ⟨117551008403771963879244971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78367338935847975919496647 117551008403771963879244971)
    ·
      refine ⟨176326512605657945818867457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117551008403771963879244971 176326512605657945818867457)
      ·
        refine ⟨132244884454243459364150593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176326512605657945818867457 132244884454243459364150593)
        ·
          refine ⟨99183663340682594523112945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132244884454243459364150593 99183663340682594523112945)
          ·
            refine ⟨74387747505511945892334709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99183663340682594523112945 74387747505511945892334709)
            ·
              refine ⟨6973851328641744927406379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74387747505511945892334709 6973851328641744927406379)
              ·
                refine ⟨10460776992962617391109569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973851328641744927406379 10460776992962617391109569)
                ·
                  refine ⟨7845582744721963043332177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10460776992962617391109569 7845582744721963043332177)
                  ·
                    refine ⟨5884187058541472282499133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7845582744721963043332177 5884187058541472282499133)
                    ·
                      refine ⟨2206570146953052105937175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5884187058541472282499133 2206570146953052105937175)
                      ·
                        rfl

theorem cell23_4297280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_4297280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297280 prefixEnd_4297280 := by exact prefixLift 4297280
  have htrace : WordTrace (prefixWord ++ tailWord_4297280) baseStart_4297280 baseEnd_4297280 := by
    simpa [prefixWord, tailWord_4297280, baseEnd_4297280] using wordTrace_append hprefix tailTrace_4297280
  have hstable : (prefixWord ++ tailWord_4297280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297280).length < 2 ^ (prefixWord ++ tailWord_4297280).sum := by decide
  have hdescent : baseEnd_4297280 < baseStart_4297280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297287 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 1, 4]
def baseStart_4297287 : Nat := 118140960795 + 4297287 * 2 ^ 59
def prefixEnd_4297287 : Nat := 4983230072969 + 3 ^ 40 * 4297287 * 2
def baseEnd_4297287 : Nat := 735524580439211192849881

theorem tailTrace_4297287 : CollatzResearch.WordTrace tailWord_4297287 prefixEnd_4297287 735524580439211192849881 := by
  unfold tailWord_4297287
  simp only [CollatzResearch.WordTrace]
  refine ⟨156734933182670592034498115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104489955455113728022998743 156734933182670592034498115)
  ·
    refine ⟨235102399774005888051747173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156734933182670592034498115 235102399774005888051747173)
    ·
      refine ⟨44081699957626104009702595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235102399774005888051747173 44081699957626104009702595)
      ·
        refine ⟨66122549936439156014553893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44081699957626104009702595 66122549936439156014553893)
        ·
          refine ⟨12397978113082341752728855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66122549936439156014553893 12397978113082341752728855)
          ·
            refine ⟨18596967169623512629093283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12397978113082341752728855 18596967169623512629093283)
            ·
              refine ⟨27895450754435268943639925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18596967169623512629093283 27895450754435268943639925)
              ·
                refine ⟨2615198508228306463466243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27895450754435268943639925 2615198508228306463466243)
                ·
                  refine ⟨3922797762342459695199365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615198508228306463466243 3922797762342459695199365)
                  ·
                    refine ⟨735524580439211192849881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3922797762342459695199365 735524580439211192849881)
                    ·
                      rfl

theorem cell23_4297287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_4297287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297287 prefixEnd_4297287 := by exact prefixLift 4297287
  have htrace : WordTrace (prefixWord ++ tailWord_4297287) baseStart_4297287 baseEnd_4297287 := by
    simpa [prefixWord, tailWord_4297287, baseEnd_4297287] using wordTrace_append hprefix tailTrace_4297287
  have hstable : (prefixWord ++ tailWord_4297287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297287).length < 2 ^ (prefixWord ++ tailWord_4297287).sum := by decide
  have hdescent : baseEnd_4297287 < baseStart_4297287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297300 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 6]
def baseStart_4297300 : Nat := 118140960795 + 4297300 * 2 ^ 59
def prefixEnd_4297300 : Nat := 4983230072969 + 3 ^ 40 * 4297300 * 2
def baseEnd_4297300 : Nat := 245175601840682447520787

theorem tailTrace_4297300 : CollatzResearch.WordTrace tailWord_4297300 prefixEnd_4297300 245175601840682447520787 := by
  unfold tailWord_4297300
  simp only [CollatzResearch.WordTrace]
  refine ⟨78367703665811747627360677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104490271554415663503147569 78367703665811747627360677)
  ·
    refine ⟨14693944437339702680130127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78367703665811747627360677 14693944437339702680130127)
    ·
      refine ⟨22040916656009554020195191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14693944437339702680130127 22040916656009554020195191)
      ·
        refine ⟨33061374984014331030292787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22040916656009554020195191 33061374984014331030292787)
        ·
          refine ⟨49592062476021496545439181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33061374984014331030292787 49592062476021496545439181)
          ·
            refine ⟨18597023428508061204539693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49592062476021496545439181 18597023428508061204539693)
            ·
              refine ⟨6973883785690522951702385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18597023428508061204539693 6973883785690522951702385)
              ·
                refine ⟨5230412839267892213776789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6973883785690522951702385 5230412839267892213776789)
                ·
                  refine ⟨245175601840682447520787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5230412839267892213776789 245175601840682447520787)
                  ·
                    rfl

theorem cell23_4297300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_4297300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297300 prefixEnd_4297300 := by exact prefixLift 4297300
  have htrace : WordTrace (prefixWord ++ tailWord_4297300) baseStart_4297300 baseEnd_4297300 := by
    simpa [prefixWord, tailWord_4297300, baseEnd_4297300] using wordTrace_append hprefix tailTrace_4297300
  have hstable : (prefixWord ++ tailWord_4297300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297300).length < 2 ^ (prefixWord ++ tailWord_4297300).sum := by decide
  have hdescent : baseEnd_4297300 < baseStart_4297300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297317 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 6]
def baseStart_4297317 : Nat := 118140960795 + 4297317 * 2 ^ 59
def prefixEnd_4297317 : Nat := 4983230072969 + 3 ^ 40 * 4297317 * 2
def baseEnd_4297317 : Nat := 245176571748585384574945

theorem tailTrace_4297317 : CollatzResearch.WordTrace tailWord_4297317 prefixEnd_4297317 245176571748585384574945 := by
  unfold tailWord_4297317
  simp only [CollatzResearch.WordTrace]
  refine ⟨156736027372561907158090205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104490684915041271438726803 156736027372561907158090205)
  ·
    refine ⟨58776010264710715184283827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156736027372561907158090205 58776010264710715184283827)
    ·
      refine ⟨88164015397066072776425741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58776010264710715184283827 88164015397066072776425741)
      ·
        refine ⟨33061505773899777291159653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88164015397066072776425741 33061505773899777291159653)
        ·
          refine ⟨6199032332606208242092435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33061505773899777291159653 6199032332606208242092435)
          ·
            refine ⟨9298548498909312363138653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6199032332606208242092435 9298548498909312363138653)
            ·
              refine ⟨3486955687090992136176995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9298548498909312363138653 3486955687090992136176995)
              ·
                refine ⟨5230433530636488204265493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486955687090992136176995 5230433530636488204265493)
                ·
                  refine ⟨245176571748585384574945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5230433530636488204265493 245176571748585384574945)
                  ·
                    rfl

theorem cell23_4297317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_4297317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297317 prefixEnd_4297317 := by exact prefixLift 4297317
  have htrace : WordTrace (prefixWord ++ tailWord_4297317) baseStart_4297317 baseEnd_4297317 := by
    simpa [prefixWord, tailWord_4297317, baseEnd_4297317] using wordTrace_append hprefix tailTrace_4297317
  have hstable : (prefixWord ++ tailWord_4297317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297317).length < 2 ^ (prefixWord ++ tailWord_4297317).sum := by decide
  have hdescent : baseEnd_4297317 < baseStart_4297317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297344 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 1, 1, 3]
def baseStart_4297344 : Nat := 118140960795 + 4297344 * 2 ^ 59
def prefixEnd_4297344 : Nat := 4983230072969 + 3 ^ 40 * 4297344 * 2
def baseEnd_4297344 : Nat := 2206603009714939855536881

theorem tailTrace_4297344 : CollatzResearch.WordTrace tailWord_4297344 prefixEnd_4297344 2206603009714939855536881 := by
  unfold tailWord_4297344
  simp only [CollatzResearch.WordTrace]
  refine ⟨78368506071732045384661543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104491341428976060512882057 78368506071732045384661543)
  ·
    refine ⟨117552759107598068076992315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78368506071732045384661543 117552759107598068076992315)
    ·
      refine ⟨176329138661397102115488473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117552759107598068076992315 176329138661397102115488473)
      ·
        refine ⟨132246853996047826586616355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176329138661397102115488473 132246853996047826586616355)
        ·
          refine ⟨198370280994071739879924533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132246853996047826586616355 198370280994071739879924533)
          ·
            refine ⟨18597213843194225613742925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198370280994071739879924533 18597213843194225613742925)
            ·
              refine ⟨6973955191197834605153597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18597213843194225613742925 6973955191197834605153597)
              ·
                refine ⟨2615233196699187976932599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6973955191197834605153597 2615233196699187976932599)
                ·
                  refine ⟨3922849795048781965398899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615233196699187976932599 3922849795048781965398899)
                  ·
                    refine ⟨5884274692573172948098349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3922849795048781965398899 5884274692573172948098349)
                    ·
                      refine ⟨2206603009714939855536881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5884274692573172948098349 2206603009714939855536881)
                      ·
                        rfl

theorem cell23_4297344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_4297344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297344 prefixEnd_4297344 := by exact prefixLift 4297344
  have htrace : WordTrace (prefixWord ++ tailWord_4297344) baseStart_4297344 baseEnd_4297344 := by
    simpa [prefixWord, tailWord_4297344, baseEnd_4297344] using wordTrace_append hprefix tailTrace_4297344
  have hstable : (prefixWord ++ tailWord_4297344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297344).length < 2 ^ (prefixWord ++ tailWord_4297344).sum := by decide
  have hdescent : baseEnd_4297344 < baseStart_4297344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297354 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_4297354 : Nat := 118140960795 + 4297354 * 2 ^ 59
def prefixEnd_4297354 : Nat := 4983230072969 + 3 ^ 40 * 4297354 * 2
def baseEnd_4297354 : Nat := 2206608144521484816411835

theorem tailTrace_4297354 : CollatzResearch.WordTrace tailWord_4297354 prefixEnd_4297354 2206608144521484816411835 := by
  unfold tailWord_4297354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39184344218356965619296779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104491584582285241651458077 39184344218356965619296779)
  ·
    refine ⟨58776516327535448428945169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39184344218356965619296779 58776516327535448428945169)
    ·
      refine ⟨44082387245651586321708877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58776516327535448428945169 44082387245651586321708877)
      ·
        refine ⟨16530895217119344870640829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44082387245651586321708877 16530895217119344870640829)
        ·
          refine ⟨6199085706419754326490311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16530895217119344870640829 6199085706419754326490311)
          ·
            refine ⟨9298628559629631489735467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6199085706419754326490311 9298628559629631489735467)
            ·
              refine ⟨13947942839444447234603201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9298628559629631489735467 13947942839444447234603201)
              ·
                refine ⟨10460957129583335425952401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13947942839444447234603201 10460957129583335425952401)
                ·
                  refine ⟨7845717847187501569464301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10460957129583335425952401 7845717847187501569464301)
                  ·
                    refine ⟨2942144192695313088549113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7845717847187501569464301 2942144192695313088549113)
                    ·
                      refine ⟨2206608144521484816411835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942144192695313088549113 2206608144521484816411835)
                      ·
                        rfl

theorem cell23_4297354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_4297354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297354 prefixEnd_4297354 := by exact prefixLift 4297354
  have htrace : WordTrace (prefixWord ++ tailWord_4297354) baseStart_4297354 baseEnd_4297354 := by
    simpa [prefixWord, tailWord_4297354, baseEnd_4297354] using wordTrace_append hprefix tailTrace_4297354
  have hstable : (prefixWord ++ tailWord_4297354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297354).length < 2 ^ (prefixWord ++ tailWord_4297354).sum := by decide
  have hdescent : baseEnd_4297354 < baseStart_4297354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297363 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4]
def baseStart_4297363 : Nat := 118140960795 + 4297363 * 2 ^ 59
def prefixEnd_4297363 : Nat := 4983230072969 + 3 ^ 40 * 4297363 * 2
def baseEnd_4297363 : Nat := 2206612765847375281199293

theorem tailTrace_4297363 : CollatzResearch.WordTrace tailWord_4297363 prefixEnd_4297363 2206612765847375281199293 := by
  unfold tailWord_4297363
  simp only [CollatzResearch.WordTrace]
  refine ⟨156737705130395257014264743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104491803420263504676176495 156737705130395257014264743)
  ·
    refine ⟨235106557695592885521397115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156737705130395257014264743 235106557695592885521397115)
    ·
      refine ⟨352659836543389328282095673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235106557695592885521397115 352659836543389328282095673)
      ·
        refine ⟨264494877407541996211571755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352659836543389328282095673 264494877407541996211571755)
        ·
          refine ⟨396742316111312994317357633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264494877407541996211571755 396742316111312994317357633)
          ·
            refine ⟨297556737083484745738018225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396742316111312994317357633 297556737083484745738018225)
            ·
              refine ⟨223167552812613559303513669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297556737083484745738018225 223167552812613559303513669)
              ·
                refine ⟨41843916152365042369408813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223167552812613559303513669 41843916152365042369408813)
                ·
                  refine ⟨15691468557136890888528305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41843916152365042369408813 15691468557136890888528305)
                  ·
                    refine ⟨11768601417852668166396229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15691468557136890888528305 11768601417852668166396229)
                    ·
                      refine ⟨2206612765847375281199293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11768601417852668166396229 2206612765847375281199293)
                      ·
                        rfl

theorem cell23_4297363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_4297363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297363 prefixEnd_4297363 := by exact prefixLift 4297363
  have htrace : WordTrace (prefixWord ++ tailWord_4297363) baseStart_4297363 baseEnd_4297363 := by
    simpa [prefixWord, tailWord_4297363, baseEnd_4297363] using wordTrace_append hprefix tailTrace_4297363
  have hstable : (prefixWord ++ tailWord_4297363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297363).length < 2 ^ (prefixWord ++ tailWord_4297363).sum := by decide
  have hdescent : baseEnd_4297363 < baseStart_4297363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297373 : List Nat := [1, 4, 2, 1, 1, 1, 3, 10]
def baseStart_4297373 : Nat := 118140960795 + 4297373 * 2 ^ 59
def prefixEnd_4297373 : Nat := 4983230072969 + 3 ^ 40 * 4297373 * 2
def baseEnd_4297373 : Nat := 81726588913108157113861

theorem tailTrace_4297373 : CollatzResearch.WordTrace tailWord_4297373 prefixEnd_4297373 81726588913108157113861 := by
  unfold tailWord_4297373
  simp only [CollatzResearch.WordTrace]
  refine ⟨156738069860359028722128773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104492046573572685814752515 156738069860359028722128773)
  ·
    refine ⟨29388388098817317885399145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156738069860359028722128773 29388388098817317885399145)
    ·
      refine ⟨22041291074112988414049359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29388388098817317885399145 22041291074112988414049359)
      ·
        refine ⟨33061936611169482621074039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22041291074112988414049359 33061936611169482621074039)
        ·
          refine ⟨49592904916754223931611059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33061936611169482621074039 49592904916754223931611059)
          ·
            refine ⟨74389357375131335897416589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49592904916754223931611059 74389357375131335897416589)
            ·
              refine ⟨27896009015674250961531221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74389357375131335897416589 27896009015674250961531221)
              ·
                refine ⟨81726588913108157113861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27896009015674250961531221 81726588913108157113861)
                ·
                  rfl

theorem cell23_4297373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 10].length) (baseStart_4297373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297373 prefixEnd_4297373 := by exact prefixLift 4297373
  have htrace : WordTrace (prefixWord ++ tailWord_4297373) baseStart_4297373 baseEnd_4297373 := by
    simpa [prefixWord, tailWord_4297373, baseEnd_4297373] using wordTrace_append hprefix tailTrace_4297373
  have hstable : (prefixWord ++ tailWord_4297373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297373).length < 2 ^ (prefixWord ++ tailWord_4297373).sum := by decide
  have hdescent : baseEnd_4297373 < baseStart_4297373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297380 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_4297380 : Nat := 118140960795 + 4297380 * 2 ^ 59
def prefixEnd_4297380 : Nat := 4983230072969 + 3 ^ 40 * 4297380 * 2
def baseEnd_4297380 : Nat := 2206621495018501714686715

theorem tailTrace_4297380 : CollatzResearch.WordTrace tailWord_4297380 prefixEnd_4297380 2206621495018501714686715 := by
  unfold tailWord_4297380
  simp only [CollatzResearch.WordTrace]
  refine ⟨78369162585666834458816797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104492216780889112611755729 78369162585666834458816797)
  ·
    refine ⟨29388435969625062922056299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78369162585666834458816797 29388435969625062922056299)
    ·
      refine ⟨44082653954437594383084449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29388435969625062922056299 44082653954437594383084449)
      ·
        refine ⟨33061990465828195787313337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44082653954437594383084449 33061990465828195787313337)
        ·
          refine ⟨24796492849371146840485003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33061990465828195787313337 24796492849371146840485003)
          ·
            refine ⟨37194739274056720260727505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24796492849371146840485003 37194739274056720260727505)
            ·
              refine ⟨27896054455542540195545629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37194739274056720260727505 27896054455542540195545629)
              ·
                refine ⟨10461020420828452573329611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27896054455542540195545629 10461020420828452573329611)
                ·
                  refine ⟨15691530631242678859994417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10461020420828452573329611 15691530631242678859994417)
                  ·
                    refine ⟨11768647973432009144995813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15691530631242678859994417 11768647973432009144995813)
                    ·
                      refine ⟨2206621495018501714686715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11768647973432009144995813 2206621495018501714686715)
                      ·
                        rfl

theorem cell23_4297380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_4297380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297380 prefixEnd_4297380 := by exact prefixLift 4297380
  have htrace : WordTrace (prefixWord ++ tailWord_4297380) baseStart_4297380 baseEnd_4297380 := by
    simpa [prefixWord, tailWord_4297380, baseEnd_4297380] using wordTrace_append hprefix tailTrace_4297380
  have hstable : (prefixWord ++ tailWord_4297380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297380).length < 2 ^ (prefixWord ++ tailWord_4297380).sum := by decide
  have hdescent : baseEnd_4297380 < baseStart_4297380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297397 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4297397 : Nat := 118140960795 + 4297397 * 2 ^ 59
def prefixEnd_4297397 : Nat := 4983230072969 + 3 ^ 40 * 4297397 * 2
def baseEnd_4297397 : Nat := 2206630224189628148174137

theorem tailTrace_4297397 : CollatzResearch.WordTrace tailWord_4297397 prefixEnd_4297397 2206630224189628148174137 := by
  unfold tailWord_4297397
  simp only [CollatzResearch.WordTrace]
  refine ⟨156738945212272080821002445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104492630141514720547334963 156738945212272080821002445)
  ·
    refine ⟨58777104454602030307875917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156738945212272080821002445 58777104454602030307875917)
    ·
      refine ⟨22041414170475761365453469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58777104454602030307875917 22041414170475761365453469)
      ·
        refine ⟨8265530313928410512045051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22041414170475761365453469 8265530313928410512045051)
        ·
          refine ⟨12398295470892615768067577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8265530313928410512045051 12398295470892615768067577)
          ·
            refine ⟨9298721603169461826050683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12398295470892615768067577 9298721603169461826050683)
            ·
              refine ⟨13948082404754192739076025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9298721603169461826050683 13948082404754192739076025)
              ·
                refine ⟨10461061803565644554307019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13948082404754192739076025 10461061803565644554307019)
                ·
                  refine ⟨15691592705348466831460529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10461061803565644554307019 15691592705348466831460529)
                  ·
                    refine ⟨11768694529011350123595397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15691592705348466831460529 11768694529011350123595397)
                    ·
                      refine ⟨2206630224189628148174137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11768694529011350123595397 2206630224189628148174137)
                      ·
                        rfl

theorem cell23_4297397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4297397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297397 prefixEnd_4297397 := by exact prefixLift 4297397
  have htrace : WordTrace (prefixWord ++ tailWord_4297397) baseStart_4297397 baseEnd_4297397 := by
    simpa [prefixWord, tailWord_4297397, baseEnd_4297397] using wordTrace_append hprefix tailTrace_4297397
  have hstable : (prefixWord ++ tailWord_4297397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297397).length < 2 ^ (prefixWord ++ tailWord_4297397).sum := by decide
  have hdescent : baseEnd_4297397 < baseStart_4297397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297404 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_4297404 : Nat := 118140960795 + 4297404 * 2 ^ 59
def prefixEnd_4297404 : Nat := 4983230072969 + 3 ^ 40 * 4297404 * 2
def baseEnd_4297404 : Nat := 2206633818554209620786605

theorem tailTrace_4297404 : CollatzResearch.WordTrace tailWord_4297404 prefixEnd_4297404 2206633818554209620786605 := by
  unfold tailWord_4297404
  simp only [CollatzResearch.WordTrace]
  refine ⟨78369600261623360508253633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104492800348831147344338177 78369600261623360508253633)
  ·
    refine ⟨58777200196217520381190225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78369600261623360508253633 58777200196217520381190225)
    ·
      refine ⟨44082900147163140285892669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58777200196217520381190225 44082900147163140285892669)
      ·
        refine ⟨16531087555186177607209751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44082900147163140285892669 16531087555186177607209751)
        ·
          refine ⟨24796631332779266410814627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16531087555186177607209751 24796631332779266410814627)
          ·
            refine ⟨37194946999168899616221941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24796631332779266410814627 37194946999168899616221941)
            ·
              refine ⟨3487026281172084339020807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37194946999168899616221941 3487026281172084339020807)
              ·
                refine ⟨5230539421758126508531211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487026281172084339020807 5230539421758126508531211)
                ·
                  refine ⟨7845809132637189762796817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5230539421758126508531211 7845809132637189762796817)
                  ·
                    refine ⟨5884356849477892322097613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7845809132637189762796817 5884356849477892322097613)
                    ·
                      refine ⟨2206633818554209620786605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5884356849477892322097613 2206633818554209620786605)
                      ·
                        rfl

theorem cell23_4297404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_4297404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297404 prefixEnd_4297404 := by exact prefixLift 4297404
  have htrace : WordTrace (prefixWord ++ tailWord_4297404) baseStart_4297404 baseEnd_4297404 := by
    simpa [prefixWord, tailWord_4297404, baseEnd_4297404] using wordTrace_append hprefix tailTrace_4297404
  have hstable : (prefixWord ++ tailWord_4297404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297404).length < 2 ^ (prefixWord ++ tailWord_4297404).sum := by decide
  have hdescent : baseEnd_4297404 < baseStart_4297404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297418 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_4297418 : Nat := 118140960795 + 4297418 * 2 ^ 59
def prefixEnd_4297418 : Nat := 4983230072969 + 3 ^ 40 * 4297418 * 2
def baseEnd_4297418 : Nat := 2206641007283372566011541

theorem tailTrace_4297418 : CollatzResearch.WordTrace tailWord_4297418 prefixEnd_4297418 2206641007283372566011541 := by
  unfold tailWord_4297418
  simp only [CollatzResearch.WordTrace]
  refine ⟨39184927786299000351879227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104493140763464000938344605 39184927786299000351879227)
  ·
    refine ⟨58777391679448500527818841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39184927786299000351879227 58777391679448500527818841)
    ·
      refine ⟨44083043759586375395864131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58777391679448500527818841 44083043759586375395864131)
      ·
        refine ⟨66124565639379563093796197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44083043759586375395864131 66124565639379563093796197)
        ·
          refine ⟨12398356057383668080086787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66124565639379563093796197 12398356057383668080086787)
          ·
            refine ⟨18597534086075502120130181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12398356057383668080086787 18597534086075502120130181)
            ·
              refine ⟨3487037641139156647524409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18597534086075502120130181 3487037641139156647524409)
              ·
                refine ⟨2615278230854367485643307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3487037641139156647524409 2615278230854367485643307)
                ·
                  refine ⟨3922917346281551228464961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615278230854367485643307 3922917346281551228464961)
                  ·
                    refine ⟨2942188009711163421348721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3922917346281551228464961 2942188009711163421348721)
                    ·
                      refine ⟨2206641007283372566011541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942188009711163421348721 2206641007283372566011541)
                      ·
                        rfl

theorem cell23_4297418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_4297418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297418 prefixEnd_4297418 := by exact prefixLift 4297418
  have htrace : WordTrace (prefixWord ++ tailWord_4297418) baseStart_4297418 baseEnd_4297418 := by
    simpa [prefixWord, tailWord_4297418, baseEnd_4297418] using wordTrace_append hprefix tailTrace_4297418
  have hstable : (prefixWord ++ tailWord_4297418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297418).length < 2 ^ (prefixWord ++ tailWord_4297418).sum := by decide
  have hdescent : baseEnd_4297418 < baseStart_4297418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297420 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_4297420 : Nat := 118140960795 + 4297420 * 2 ^ 59
def prefixEnd_4297420 : Nat := 4983230072969 + 3 ^ 40 * 4297420 * 2
def baseEnd_4297420 : Nat := 735547344748227186062177

theorem tailTrace_4297420 : CollatzResearch.WordTrace tailWord_4297420 prefixEnd_4297420 735547344748227186062177 := by
  unfold tailWord_4297420
  simp only [CollatzResearch.WordTrace]
  refine ⟨78369892045594377874544857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104493189394125837166059809 78369892045594377874544857)
  ·
    refine ⟨58777419034195783405908643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78369892045594377874544857 58777419034195783405908643)
    ·
      refine ⟨88166128551293675108862965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58777419034195783405908643 88166128551293675108862965)
      ·
        refine ⟨8265574551683782041455903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88166128551293675108862965 8265574551683782041455903)
        ·
          refine ⟨12398361827525673062183855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8265574551683782041455903 12398361827525673062183855)
          ·
            refine ⟨18597542741288509593275783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12398361827525673062183855 18597542741288509593275783)
            ·
              refine ⟨27896314111932764389913675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18597542741288509593275783 27896314111932764389913675)
              ·
                refine ⟨41844471167899146584870513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27896314111932764389913675 41844471167899146584870513)
                ·
                  refine ⟨31383353375924359938652885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41844471167899146584870513 31383353375924359938652885)
                  ·
                    refine ⟨735547344748227186062177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31383353375924359938652885 735547344748227186062177)
                    ·
                      rfl

theorem cell23_4297420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_4297420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297420 prefixEnd_4297420 := by exact prefixLift 4297420
  have htrace : WordTrace (prefixWord ++ tailWord_4297420) baseStart_4297420 baseEnd_4297420 := by
    simpa [prefixWord, tailWord_4297420, baseEnd_4297420] using wordTrace_append hprefix tailTrace_4297420
  have hstable : (prefixWord ++ tailWord_4297420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297420).length < 2 ^ (prefixWord ++ tailWord_4297420).sum := by decide
  have hdescent : baseEnd_4297420 < baseStart_4297420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297457 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 1, 4, 2]
def baseStart_4297457 : Nat := 118140960795 + 4297457 * 2 ^ 59
def prefixEnd_4297457 : Nat := 4983230072969 + 3 ^ 40 * 4297457 * 2
def baseEnd_4297457 : Nat := 2206661033028897913423861

theorem tailTrace_4297457 : CollatzResearch.WordTrace tailWord_4297457 prefixEnd_4297457 2206661033028897913423861 := by
  unfold tailWord_4297457
  simp only [CollatzResearch.WordTrace]
  refine ⟨156741133592054711068186625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104494089061369807378791083 156741133592054711068186625)
  ·
    refine ⟨117555850194041033301139969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156741133592054711068186625 117555850194041033301139969)
    ·
      refine ⟨88166887645530774975854977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117555850194041033301139969 88166887645530774975854977)
      ·
        refine ⟨66125165734148081231891233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88166887645530774975854977 66125165734148081231891233)
        ·
          refine ⟨49593874300611060923918425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66125165734148081231891233 49593874300611060923918425)
          ·
            refine ⟨37195405725458295692938819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49593874300611060923918425 37195405725458295692938819)
            ·
              refine ⟨55793108588187443539408229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37195405725458295692938819 55793108588187443539408229)
              ·
                refine ⟨10461207860285145663639043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55793108588187443539408229 10461207860285145663639043)
                ·
                  refine ⟨15691811790427718495458565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10461207860285145663639043 15691811790427718495458565)
                  ·
                    refine ⟨2942214710705197217898481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15691811790427718495458565 2942214710705197217898481)
                    ·
                      refine ⟨2206661033028897913423861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942214710705197217898481 2206661033028897913423861)
                      ·
                        rfl

theorem cell23_4297457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_4297457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297457 prefixEnd_4297457 := by exact prefixLift 4297457
  have htrace : WordTrace (prefixWord ++ tailWord_4297457) baseStart_4297457 baseEnd_4297457 := by
    simpa [prefixWord, tailWord_4297457, baseEnd_4297457] using wordTrace_append hprefix tailTrace_4297457
  have hstable : (prefixWord ++ tailWord_4297457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297457).length < 2 ^ (prefixWord ++ tailWord_4297457).sum := by decide
  have hdescent : baseEnd_4297457 < baseStart_4297457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297463 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 11]
def baseStart_4297463 : Nat := 118140960795 + 4297463 * 2 ^ 59
def prefixEnd_4297463 : Nat := 4983230072969 + 3 ^ 40 * 4297463 * 2
def baseEnd_4297463 : Nat := 245184901545869432216537

theorem tailTrace_4297463 : CollatzResearch.WordTrace tailWord_4297463 prefixEnd_4297463 245184901545869432216537 := by
  unfold tailWord_4297463
  simp only [CollatzResearch.WordTrace]
  refine ⟨156741352430032974092905043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104494234953355316061936695 156741352430032974092905043)
  ·
    refine ⟨235112028645049461139357565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156741352430032974092905043 235112028645049461139357565)
    ·
      refine ⟨88167010741893547927259087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235112028645049461139357565 88167010741893547927259087)
      ·
        refine ⟨132250516112840321890888631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88167010741893547927259087 132250516112840321890888631)
        ·
          refine ⟨198375774169260482836332947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132250516112840321890888631 198375774169260482836332947)
          ·
            refine ⟨297563661253890724254499421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198375774169260482836332947 297563661253890724254499421)
            ·
              refine ⟨111586372970209021595437283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297563661253890724254499421 111586372970209021595437283)
              ·
                refine ⟨167379559455313532393155925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111586372970209021595437283 167379559455313532393155925)
                ·
                  refine ⟨245184901545869432216537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 167379559455313532393155925 245184901545869432216537)
                  ·
                    rfl

theorem cell23_4297463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 11].length) (baseStart_4297463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297463 prefixEnd_4297463 := by exact prefixLift 4297463
  have htrace : WordTrace (prefixWord ++ tailWord_4297463) baseStart_4297463 baseEnd_4297463 := by
    simpa [prefixWord, tailWord_4297463, baseEnd_4297463] using wordTrace_append hprefix tailTrace_4297463
  have hstable : (prefixWord ++ tailWord_4297463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297463).length < 2 ^ (prefixWord ++ tailWord_4297463).sum := by decide
  have hdescent : baseEnd_4297463 < baseStart_4297463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297480 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 7]
def baseStart_4297480 : Nat := 118140960795 + 4297480 * 2 ^ 59
def prefixEnd_4297480 : Nat := 4983230072969 + 3 ^ 40 * 4297480 * 2
def baseEnd_4297480 : Nat := 245185871453772369270695

theorem tailTrace_4297480 : CollatzResearch.WordTrace tailWord_4297480 prefixEnd_4297480 245185871453772369270695 := by
  unfold tailWord_4297480
  simp only [CollatzResearch.WordTrace]
  refine ⟨78370986235485692998136947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104494648313980923997515929 78370986235485692998136947)
  ·
    refine ⟨117556479353228539497205421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78370986235485692998136947 117556479353228539497205421)
    ·
      refine ⟨44083679757460702311452033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117556479353228539497205421 44083679757460702311452033)
      ·
        refine ⟨33062759818095526733589025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44083679757460702311452033 33062759818095526733589025)
        ·
          refine ⟨24797069863571645050191769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33062759818095526733589025 24797069863571645050191769)
          ·
            refine ⟨18597802397678733787643827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24797069863571645050191769 18597802397678733787643827)
            ·
              refine ⟨27896703596518100681465741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18597802397678733787643827 27896703596518100681465741)
              ·
                refine ⟨10461263848694287755549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27896703596518100681465741 10461263848694287755549653)
                ·
                  refine ⟨245185871453772369270695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10461263848694287755549653 245185871453772369270695)
                  ·
                    rfl

theorem cell23_4297480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_4297480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297480 prefixEnd_4297480 := by exact prefixLift 4297480
  have htrace : WordTrace (prefixWord ++ tailWord_4297480) baseStart_4297480 baseEnd_4297480 := by
    simpa [prefixWord, tailWord_4297480, baseEnd_4297480] using wordTrace_append hprefix tailTrace_4297480
  have hstable : (prefixWord ++ tailWord_4297480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297480).length < 2 ^ (prefixWord ++ tailWord_4297480).sum := by decide
  have hdescent : baseEnd_4297480 < baseStart_4297480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297491 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 2, 2, 2]
def baseStart_4297491 : Nat := 118140960795 + 4297491 * 2 ^ 59
def prefixEnd_4297491 : Nat := 4983230072969 + 3 ^ 40 * 4297491 * 2
def baseEnd_4297491 : Nat := 2206678491371150780398705

theorem tailTrace_4297491 : CollatzResearch.WordTrace tailWord_4297491 prefixEnd_4297491 2206678491371150780398705 := by
  unfold tailWord_4297491
  simp only [CollatzResearch.WordTrace]
  refine ⟨156742373673931534874924327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104494915782621023249949551 156742373673931534874924327)
  ·
    refine ⟨235113560510897302312386491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156742373673931534874924327 235113560510897302312386491)
    ·
      refine ⟨352670340766345953468579737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235113560510897302312386491 352670340766345953468579737)
      ·
        refine ⟨264502755574759465101434803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352670340766345953468579737 264502755574759465101434803)
        ·
          refine ⟨396754133362139197652152205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264502755574759465101434803 396754133362139197652152205)
          ·
            refine ⟨148782800010802199119557077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396754133362139197652152205 148782800010802199119557077)
            ·
              refine ⟨3487096875253176541864619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148782800010802199119557077 3487096875253176541864619)
              ·
                refine ⟨5230645312879764812796929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487096875253176541864619 5230645312879764812796929)
                ·
                  refine ⟨3922983984659823609597697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5230645312879764812796929 3922983984659823609597697)
                  ·
                    refine ⟨2942237988494867707198273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3922983984659823609597697 2942237988494867707198273)
                    ·
                      refine ⟨2206678491371150780398705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942237988494867707198273 2206678491371150780398705)
                      ·
                        rfl

theorem cell23_4297491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 2, 2].length) (baseStart_4297491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297491 prefixEnd_4297491 := by exact prefixLift 4297491
  have htrace : WordTrace (prefixWord ++ tailWord_4297491) baseStart_4297491 baseEnd_4297491 := by
    simpa [prefixWord, tailWord_4297491, baseEnd_4297491] using wordTrace_append hprefix tailTrace_4297491
  have hstable : (prefixWord ++ tailWord_4297491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297491).length < 2 ^ (prefixWord ++ tailWord_4297491).sum := by decide
  have hdescent : baseEnd_4297491 < baseStart_4297491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297550 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_4297550 : Nat := 118140960795 + 4297550 * 2 ^ 59
def prefixEnd_4297550 : Nat := 4983230072969 + 3 ^ 40 * 4297550 * 2
def baseEnd_4297550 : Nat := 2206708786729766049560933

theorem tailTrace_4297550 : CollatzResearch.WordTrace tailWord_4297550 prefixEnd_4297550 2206708786729766049560933 := by
  unfold tailWord_4297550
  simp only [CollatzResearch.WordTrace]
  refine ⟨19593065697589723493915263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104496350387145191967548069 19593065697589723493915263)
  ·
    refine ⟨29389598546384585240872895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19593065697589723493915263 29389598546384585240872895)
    ·
      refine ⟨44084397819576877861309343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29389598546384585240872895 44084397819576877861309343)
      ·
        refine ⟨66126596729365316791964015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44084397819576877861309343 66126596729365316791964015)
        ·
          refine ⟨99189895094047975187946023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66126596729365316791964015 99189895094047975187946023)
          ·
            refine ⟨148784842641071962781919035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99189895094047975187946023 148784842641071962781919035)
            ·
              refine ⟨223177263961607944172878553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148784842641071962781919035 223177263961607944172878553)
              ·
                refine ⟨167382947971205958129658915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223177263961607944172878553 167382947971205958129658915)
                ·
                  refine ⟨251074421956808937194488373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167382947971205958129658915 251074421956808937194488373)
                  ·
                    refine ⟨23538227058450837861983285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 251074421956808937194488373 23538227058450837861983285)
                    ·
                      refine ⟨2206708786729766049560933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23538227058450837861983285 2206708786729766049560933)
                      ·
                        rfl

theorem cell23_4297550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_4297550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297550 prefixEnd_4297550 := by exact prefixLift 4297550
  have htrace : WordTrace (prefixWord ++ tailWord_4297550) baseStart_4297550 baseEnd_4297550 := by
    simpa [prefixWord, tailWord_4297550, baseEnd_4297550] using wordTrace_append hprefix tailTrace_4297550
  have hstable : (prefixWord ++ tailWord_4297550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297550).length < 2 ^ (prefixWord ++ tailWord_4297550).sum := by decide
  have hdescent : baseEnd_4297550 < baseStart_4297550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297557 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_4297557 : Nat := 118140960795 + 4297557 * 2 ^ 59
def prefixEnd_4297557 : Nat := 4983230072969 + 3 ^ 40 * 4297557 * 2
def baseEnd_4297557 : Nat := 735570793698115840724467

theorem tailTrace_4297557 : CollatzResearch.WordTrace tailWord_4297557 prefixEnd_4297557 735570793698115840724467 := by
  unfold tailWord_4297557
  simp only [CollatzResearch.WordTrace]
  refine ⟨156744780891692428146826925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104496520594461618764551283 156744780891692428146826925)
  ·
    refine ⟨58779292834384660555060097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156744780891692428146826925 58779292834384660555060097)
    ·
      refine ⟨44084469625788495416295073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58779292834384660555060097 44084469625788495416295073)
      ·
        refine ⟨33063352219341371562221305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44084469625788495416295073 33063352219341371562221305)
        ·
          refine ⟨24797514164506028671665979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33063352219341371562221305 24797514164506028671665979)
          ·
            refine ⟨37196271246759043007498969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24797514164506028671665979 37196271246759043007498969)
            ·
              refine ⟨27897203435069282255624227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37196271246759043007498969 27897203435069282255624227)
              ·
                refine ⟨41845805152603923383436341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27897203435069282255624227 41845805152603923383436341)
                ·
                  refine ⟨3923044233056617817197157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41845805152603923383436341 3923044233056617817197157)
                  ·
                    refine ⟨735570793698115840724467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923044233056617817197157 735570793698115840724467)
                    ·
                      rfl

theorem cell23_4297557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_4297557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297557 prefixEnd_4297557 := by exact prefixLift 4297557
  have htrace : WordTrace (prefixWord ++ tailWord_4297557) baseStart_4297557 baseEnd_4297557 := by
    simpa [prefixWord, tailWord_4297557, baseEnd_4297557] using wordTrace_append hprefix tailTrace_4297557
  have hstable : (prefixWord ++ tailWord_4297557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297557).length < 2 ^ (prefixWord ++ tailWord_4297557).sum := by decide
  have hdescent : baseEnd_4297557 < baseStart_4297557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297560 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_4297560 : Nat := 118140960795 + 4297560 * 2 ^ 59
def prefixEnd_4297560 : Nat := 4983230072969 + 3 ^ 40 * 4297560 * 2
def baseEnd_4297560 : Nat := 2206713921536311010435887

theorem tailTrace_4297560 : CollatzResearch.WordTrace tailWord_4297560 prefixEnd_4297560 2206713921536311010435887 := by
  unfold tailWord_4297560
  simp only [CollatzResearch.WordTrace]
  refine ⟨78372445155340779829593067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104496593540454373106124089 78372445155340779829593067)
  ·
    refine ⟨117558667733011169744389601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78372445155340779829593067 117558667733011169744389601)
    ·
      refine ⟨88169000799758377308292201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117558667733011169744389601 88169000799758377308292201)
      ·
        refine ⟨66126750599818782981219151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88169000799758377308292201 66126750599818782981219151)
        ·
          refine ⟨99190125899728174471828727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66126750599818782981219151 99190125899728174471828727)
          ·
            refine ⟨148785188849592261707743091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99190125899728174471828727 148785188849592261707743091)
            ·
              refine ⟨223177783274388392561614637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148785188849592261707743091 223177783274388392561614637)
              ·
                refine ⟨83691668727895647210605489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223177783274388392561614637 83691668727895647210605489)
                ·
                  refine ⟨62768751545921735407954117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83691668727895647210605489 62768751545921735407954117)
                  ·
                    refine ⟨11769140914860325388991397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62768751545921735407954117 11769140914860325388991397)
                    ·
                      refine ⟨2206713921536311010435887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11769140914860325388991397 2206713921536311010435887)
                      ·
                        rfl

theorem cell23_4297560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_4297560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297560 prefixEnd_4297560 := by exact prefixLift 4297560
  have htrace : WordTrace (prefixWord ++ tailWord_4297560) baseStart_4297560 baseEnd_4297560 := by
    simpa [prefixWord, tailWord_4297560, baseEnd_4297560] using wordTrace_append hprefix tailTrace_4297560
  have hstable : (prefixWord ++ tailWord_4297560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297560).length < 2 ^ (prefixWord ++ tailWord_4297560).sum := by decide
  have hdescent : baseEnd_4297560 < baseStart_4297560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297564 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4297564 : Nat := 118140960795 + 4297564 * 2 ^ 59
def prefixEnd_4297564 : Nat := 4983230072969 + 3 ^ 40 * 4297564 * 2
def baseEnd_4297564 : Nat := 2206715975458928994785869

theorem tailTrace_4297564 : CollatzResearch.WordTrace tailWord_4297564 prefixEnd_4297564 2206715975458928994785869 := by
  unfold tailWord_4297564
  simp only [CollatzResearch.WordTrace]
  refine ⟨78372518101333534171165873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104496690801778045561554497 78372518101333534171165873)
  ·
    refine ⟨58779388576000150628374405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78372518101333534171165873 58779388576000150628374405)
    ·
      refine ⟨11021135358000028242820201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58779388576000150628374405 11021135358000028242820201)
      ·
        refine ⟨8265851518500021182115151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11021135358000028242820201 8265851518500021182115151)
        ·
          refine ⟨12398777277750031773172727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8265851518500021182115151 12398777277750031773172727)
          ·
            refine ⟨18598165916625047659759091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12398777277750031773172727 18598165916625047659759091)
            ·
              refine ⟨27897248874937571489638637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18598165916625047659759091 27897248874937571489638637)
              ·
                refine ⟨10461468328101589308614489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27897248874937571489638637 10461468328101589308614489)
                ·
                  refine ⟨7846101246076191981460867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10461468328101589308614489 7846101246076191981460867)
                  ·
                    refine ⟨11769151869114287972191301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7846101246076191981460867 11769151869114287972191301)
                    ·
                      refine ⟨2206715975458928994785869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11769151869114287972191301 2206715975458928994785869)
                      ·
                        rfl

theorem cell23_4297564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4297564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297564 prefixEnd_4297564 := by exact prefixLift 4297564
  have htrace : WordTrace (prefixWord ++ tailWord_4297564) baseStart_4297564 baseEnd_4297564 := by
    simpa [prefixWord, tailWord_4297564, baseEnd_4297564] using wordTrace_append hprefix tailTrace_4297564
  have hstable : (prefixWord ++ tailWord_4297564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297564).length < 2 ^ (prefixWord ++ tailWord_4297564).sum := by decide
  have hdescent : baseEnd_4297564 < baseStart_4297564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297598 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4297598 : Nat := 118140960795 + 4297598 * 2 ^ 59
def prefixEnd_4297598 : Nat := 4983230072969 + 3 ^ 40 * 4297598 * 2
def baseEnd_4297598 : Nat := 2206733433801181861760713

theorem tailTrace_4297598 : CollatzResearch.WordTrace tailWord_4297598 prefixEnd_4297598 2206733433801181861760713 := by
  unfold tailWord_4297598
  simp only [CollatzResearch.WordTrace]
  refine ⟨19593284535567986518633681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104497517523029261432712965 19593284535567986518633681)
  ·
    refine ⟨14694963401675989888975261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19593284535567986518633681 14694963401675989888975261)
    ·
      refine ⟨5510611275628496208365723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14694963401675989888975261 5510611275628496208365723)
      ·
        refine ⟨8265916913442744312548585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510611275628496208365723 8265916913442744312548585)
        ·
          refine ⟨6199437685082058234411439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8265916913442744312548585 6199437685082058234411439)
          ·
            refine ⟨9299156527623087351617159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6199437685082058234411439 9299156527623087351617159)
            ·
              refine ⟨13948734791434631027425739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9299156527623087351617159 13948734791434631027425739)
              ·
                refine ⟨20923102187151946541138609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13948734791434631027425739 20923102187151946541138609)
                ·
                  refine ⟨15692326640363959905853957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20923102187151946541138609 15692326640363959905853957)
                  ·
                    refine ⟨2942311245068242482347617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15692326640363959905853957 2942311245068242482347617)
                    ·
                      refine ⟨2206733433801181861760713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942311245068242482347617 2206733433801181861760713)
                      ·
                        rfl

theorem cell23_4297598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4297598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297598 prefixEnd_4297598 := by exact prefixLift 4297598
  have htrace : WordTrace (prefixWord ++ tailWord_4297598) baseStart_4297598 baseEnd_4297598 := by
    simpa [prefixWord, tailWord_4297598, baseEnd_4297598] using wordTrace_append hprefix tailTrace_4297598
  have hstable : (prefixWord ++ tailWord_4297598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297598).length < 2 ^ (prefixWord ++ tailWord_4297598).sum := by decide
  have hdescent : baseEnd_4297598 < baseStart_4297598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297617 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 1, 5]
def baseStart_4297617 : Nat := 118140960795 + 4297617 * 2 ^ 59
def prefixEnd_4297617 : Nat := 4983230072969 + 3 ^ 40 * 4297617 * 2
def baseEnd_4297617 : Nat := 735581063311205762474375

theorem tailTrace_4297617 : CollatzResearch.WordTrace tailWord_4297617 prefixEnd_4297617 735581063311205762474375 := by
  unfold tailWord_4297617
  simp only [CollatzResearch.WordTrace]
  refine ⟨156746969271475058394011105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104497979514316705596007403 156746969271475058394011105)
  ·
    refine ⟨117560226953606293795508329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156746969271475058394011105 117560226953606293795508329)
    ·
      refine ⟨88170170215204720346631247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117560226953606293795508329 88170170215204720346631247)
      ·
        refine ⟨132255255322807080519946871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88170170215204720346631247 132255255322807080519946871)
        ·
          refine ⟨198382882984210620779920307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132255255322807080519946871 198382882984210620779920307)
          ·
            refine ⟨297574324476315931169880461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198382882984210620779920307 297574324476315931169880461)
            ·
              refine ⟨111590371678618474188705173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297574324476315931169880461 111590371678618474188705173)
              ·
                refine ⟨5230798672435240977595555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111590371678618474188705173 5230798672435240977595555)
                ·
                  refine ⟨7846198008652861466393333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5230798672435240977595555 7846198008652861466393333)
                  ·
                    refine ⟨735581063311205762474375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7846198008652861466393333 735581063311205762474375)
                    ·
                      rfl

theorem cell23_4297617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_4297617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297617 prefixEnd_4297617 := by exact prefixLift 4297617
  have htrace : WordTrace (prefixWord ++ tailWord_4297617) baseStart_4297617 baseEnd_4297617 := by
    simpa [prefixWord, tailWord_4297617, baseEnd_4297617] using wordTrace_append hprefix tailTrace_4297617
  have hstable : (prefixWord ++ tailWord_4297617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297617).length < 2 ^ (prefixWord ++ tailWord_4297617).sum := by decide
  have hdescent : baseEnd_4297617 < baseStart_4297617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297618 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4297618 : Nat := 118140960795 + 4297618 * 2 ^ 59
def prefixEnd_4297618 : Nat := 4983230072969 + 3 ^ 40 * 4297618 * 2
def baseEnd_4297618 : Nat := 2206743703414271783510621

theorem tailTrace_4297618 : CollatzResearch.WordTrace tailWord_4297618 prefixEnd_4297618 2206743703414271783510621 := by
  unfold tailWord_4297618
  simp only [CollatzResearch.WordTrace]
  refine ⟨39186751436117858891199377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104498003829647623709865005 39186751436117858891199377)
  ·
    refine ⟨29390063577088394168399533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39186751436117858891199377 29390063577088394168399533)
    ·
      refine ⟨11021273841408147813149825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29390063577088394168399533 11021273841408147813149825)
      ·
        refine ⟨8265955381056110859862369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11021273841408147813149825 8265955381056110859862369)
        ·
          refine ⟨6199466535792083144896777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8265955381056110859862369 6199466535792083144896777)
          ·
            refine ⟨4649599901844062358672583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6199466535792083144896777 4649599901844062358672583)
            ·
              refine ⟨6974399852766093538008875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649599901844062358672583 6974399852766093538008875)
              ·
                refine ⟨10461599779149140307013313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6974399852766093538008875 10461599779149140307013313)
                ·
                  refine ⟨7846199834361855230259985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10461599779149140307013313 7846199834361855230259985)
                  ·
                    refine ⟨5884649875771391422694989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7846199834361855230259985 5884649875771391422694989)
                    ·
                      refine ⟨2206743703414271783510621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5884649875771391422694989 2206743703414271783510621)
                      ·
                        rfl

theorem cell23_4297618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4297618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297618 prefixEnd_4297618 := by exact prefixLift 4297618
  have htrace : WordTrace (prefixWord ++ tailWord_4297618) baseStart_4297618 baseEnd_4297618 := by
    simpa [prefixWord, tailWord_4297618, baseEnd_4297618] using wordTrace_append hprefix tailTrace_4297618
  have hstable : (prefixWord ++ tailWord_4297618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297618).length < 2 ^ (prefixWord ++ tailWord_4297618).sum := by decide
  have hdescent : baseEnd_4297618 < baseStart_4297618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297657 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4297657 : Nat := 118140960795 + 4297657 * 2 ^ 59
def prefixEnd_4297657 : Nat := 4983230072969 + 3 ^ 40 * 4297657 * 2
def baseEnd_4297657 : Nat := 2206763729159797130922941

theorem tailTrace_4297657 : CollatzResearch.WordTrace tailWord_4297657 prefixEnd_4297657 2206763729159797130922941 := by
  unfold tailWord_4297657
  simp only [CollatzResearch.WordTrace]
  refine ⟨156748428191330145225467225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104498952127553430150311483 156748428191330145225467225)
  ·
    refine ⟨117561321143497608919100419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156748428191330145225467225 117561321143497608919100419)
    ·
      refine ⟨176341981715246413378650629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117561321143497608919100419 176341981715246413378650629)
      ·
        refine ⟨33064121571608702508496993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176341981715246413378650629 33064121571608702508496993)
        ·
          refine ⟨24798091178706526881372745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33064121571608702508496993 24798091178706526881372745)
          ·
            refine ⟨18598568384029895161029559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24798091178706526881372745 18598568384029895161029559)
            ·
              refine ⟨27897852576044842741544339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18598568384029895161029559 27897852576044842741544339)
              ·
                refine ⟨41846778864067264112316509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27897852576044842741544339 41846778864067264112316509)
                ·
                  refine ⟨15692542074025224042118691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41846778864067264112316509 15692542074025224042118691)
                  ·
                    refine ⟨23538813111037836063178037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15692542074025224042118691 23538813111037836063178037)
                    ·
                      refine ⟨2206763729159797130922941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23538813111037836063178037 2206763729159797130922941)
                      ·
                        rfl

theorem cell23_4297657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4297657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297657 prefixEnd_4297657 := by exact prefixLift 4297657
  have htrace : WordTrace (prefixWord ++ tailWord_4297657) baseStart_4297657 baseEnd_4297657 := by
    simpa [prefixWord, tailWord_4297657, baseEnd_4297657] using wordTrace_append hprefix tailTrace_4297657
  have hstable : (prefixWord ++ tailWord_4297657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297657).length < 2 ^ (prefixWord ++ tailWord_4297657).sum := by decide
  have hdescent : baseEnd_4297657 < baseStart_4297657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297664 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 1, 6]
def baseStart_4297664 : Nat := 118140960795 + 4297664 * 2 ^ 59
def prefixEnd_4297664 : Nat := 4983230072969 + 3 ^ 40 * 4297664 * 2
def baseEnd_4297664 : Nat := 735589107841459534511803

theorem tailTrace_4297664 : CollatzResearch.WordTrace tailWord_4297664 prefixEnd_4297664 735589107841459534511803 := by
  unfold tailWord_4297664
  simp only [CollatzResearch.WordTrace]
  refine ⟨78374341751152392710486023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104499122334869856947314697 78374341751152392710486023)
  ·
    refine ⟨117561512626728589065729035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78374341751152392710486023 117561512626728589065729035)
    ·
      refine ⟨176342268940092883598593553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117561512626728589065729035 176342268940092883598593553)
      ·
        refine ⟨132256701705069662698945165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176342268940092883598593553 132256701705069662698945165)
        ·
          refine ⟨49596263139401123512104437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132256701705069662698945165 49596263139401123512104437)
          ·
            refine ⟨4649649669318855329259791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49596263139401123512104437 4649649669318855329259791)
            ·
              refine ⟨6974474503978282993889687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649649669318855329259791 6974474503978282993889687)
              ·
                refine ⟨10461711755967424490834531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6974474503978282993889687 10461711755967424490834531)
                ·
                  refine ⟨15692567633951136736251797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10461711755967424490834531 15692567633951136736251797)
                  ·
                    refine ⟨735589107841459534511803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15692567633951136736251797 735589107841459534511803)
                    ·
                      rfl

theorem cell23_4297664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_4297664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297664 prefixEnd_4297664 := by exact prefixLift 4297664
  have htrace : WordTrace (prefixWord ++ tailWord_4297664) baseStart_4297664 baseEnd_4297664 := by
    simpa [prefixWord, tailWord_4297664, baseEnd_4297664] using wordTrace_append hprefix tailTrace_4297664
  have hstable : (prefixWord ++ tailWord_4297664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297664).length < 2 ^ (prefixWord ++ tailWord_4297664).sum := by decide
  have hdescent : baseEnd_4297664 < baseStart_4297664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297668 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_4297668 : Nat := 118140960795 + 4297668 * 2 ^ 59
def prefixEnd_4297668 : Nat := 4983230072969 + 3 ^ 40 * 4297668 * 2
def baseEnd_4297668 : Nat := 735589792482332195961797

theorem tailTrace_4297668 : CollatzResearch.WordTrace tailWord_4297668 prefixEnd_4297668 735589792482332195961797 := by
  unfold tailWord_4297668
  simp only [CollatzResearch.WordTrace]
  refine ⟨78374414697145147052058829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104499219596193529402745105 78374414697145147052058829)
  ·
    refine ⟨29390405511429430144522061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78374414697145147052058829 29390405511429430144522061)
    ·
      refine ⟨11021402066786036304195773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29390405511429430144522061 11021402066786036304195773)
      ·
        refine ⟨4133025775044763614073415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11021402066786036304195773 4133025775044763614073415)
        ·
          refine ⟨6199538662567145421110123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133025775044763614073415 6199538662567145421110123)
          ·
            refine ⟨9299307993850718131665185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6199538662567145421110123 9299307993850718131665185)
            ·
              refine ⟨6974480995388038598748889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9299307993850718131665185 6974480995388038598748889)
              ·
                refine ⟨5230860746541028949061667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6974480995388038598748889 5230860746541028949061667)
                ·
                  refine ⟨7846291119811543423592501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5230860746541028949061667 7846291119811543423592501)
                  ·
                    refine ⟨735589792482332195961797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7846291119811543423592501 735589792482332195961797)
                    ·
                      rfl

theorem cell23_4297668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_4297668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297668 prefixEnd_4297668 := by exact prefixLift 4297668
  have htrace : WordTrace (prefixWord ++ tailWord_4297668) baseStart_4297668 baseEnd_4297668 := by
    simpa [prefixWord, tailWord_4297668, baseEnd_4297668] using wordTrace_append hprefix tailTrace_4297668
  have hstable : (prefixWord ++ tailWord_4297668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297668).length < 2 ^ (prefixWord ++ tailWord_4297668).sum := by decide
  have hdescent : baseEnd_4297668 < baseStart_4297668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297671 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_4297671 : Nat := 118140960795 + 4297671 * 2 ^ 59
def prefixEnd_4297671 : Nat := 4983230072969 + 3 ^ 40 * 4297671 * 2
def baseEnd_4297671 : Nat := 2206770917888960076147877

theorem tailTrace_4297671 : CollatzResearch.WordTrace tailWord_4297671 prefixEnd_4297671 2206770917888960076147877 := by
  unfold tailWord_4297671
  simp only [CollatzResearch.WordTrace]
  refine ⟨156748938813279425616476867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104499292542186283744317911 156748938813279425616476867)
  ·
    refine ⟨235123408219919138424715301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156748938813279425616476867 235123408219919138424715301)
    ·
      refine ⟨44085639041234838454634119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235123408219919138424715301 44085639041234838454634119)
      ·
        refine ⟨66128458561852257681951179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44085639041234838454634119 66128458561852257681951179)
        ·
          refine ⟨99192687842778386522926769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66128458561852257681951179 99192687842778386522926769)
          ·
            refine ⟨74394515882083789892195077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99192687842778386522926769 74394515882083789892195077)
            ·
              refine ⟨13948971727890710604786577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74394515882083789892195077 13948971727890710604786577)
              ·
                refine ⟨10461728795918032953589933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13948971727890710604786577 10461728795918032953589933)
                ·
                  refine ⟨3923148298469262357596225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10461728795918032953589933 3923148298469262357596225)
                  ·
                    refine ⟨2942361223851946768197169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923148298469262357596225 2942361223851946768197169)
                    ·
                      refine ⟨2206770917888960076147877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942361223851946768197169 2206770917888960076147877)
                      ·
                        rfl

theorem cell23_4297671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_4297671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297671 prefixEnd_4297671 := by exact prefixLift 4297671
  have htrace : WordTrace (prefixWord ++ tailWord_4297671) baseStart_4297671 baseEnd_4297671 := by
    simpa [prefixWord, tailWord_4297671, baseEnd_4297671] using wordTrace_append hprefix tailTrace_4297671
  have hstable : (prefixWord ++ tailWord_4297671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297671).length < 2 ^ (prefixWord ++ tailWord_4297671).sum := by decide
  have hdescent : baseEnd_4297671 < baseStart_4297671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297721 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 3]
def baseStart_4297721 : Nat := 118140960795 + 4297721 * 2 ^ 59
def prefixEnd_4297721 : Nat := 4983230072969 + 3 ^ 40 * 4297721 * 2
def baseEnd_4297721 : Nat := 2206796591921684880522647

theorem tailTrace_4297721 : CollatzResearch.WordTrace tailWord_4297721 prefixEnd_4297721 2206796591921684880522647 := by
  unfold tailWord_4297721
  simp only [CollatzResearch.WordTrace]
  refine ⟨156750762463098284155797017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104500508308732189437198011 156750762463098284155797017)
  ·
    refine ⟨117563071847323713116847763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156750762463098284155797017 117563071847323713116847763)
    ·
      refine ⟨176344607770985569675271645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117563071847323713116847763 176344607770985569675271645)
      ·
        refine ⟨66129227914119588628226867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176344607770985569675271645 66129227914119588628226867)
        ·
          refine ⟨99193841871179382942340301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66129227914119588628226867 99193841871179382942340301)
          ·
            refine ⟨37197690701692268603377613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99193841871179382942340301 37197690701692268603377613)
            ·
              refine ⟨13949134013134600726266605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37197690701692268603377613 13949134013134600726266605)
              ·
                refine ⟨5230925254925475272349977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13949134013134600726266605 5230925254925475272349977)
                ·
                  refine ⟨3923193941194106454262483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5230925254925475272349977 3923193941194106454262483)
                  ·
                    refine ⟨5884790911791159681393725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3923193941194106454262483 5884790911791159681393725)
                    ·
                      refine ⟨2206796591921684880522647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5884790911791159681393725 2206796591921684880522647)
                      ·
                        rfl

theorem cell23_4297721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_4297721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297721 prefixEnd_4297721 := by exact prefixLift 4297721
  have htrace : WordTrace (prefixWord ++ tailWord_4297721) baseStart_4297721 baseEnd_4297721 := by
    simpa [prefixWord, tailWord_4297721, baseEnd_4297721] using wordTrace_append hprefix tailTrace_4297721
  have hstable : (prefixWord ++ tailWord_4297721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297721).length < 2 ^ (prefixWord ++ tailWord_4297721).sum := by decide
  have hdescent : baseEnd_4297721 < baseStart_4297721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297778 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_4297778 : Nat := 118140960795 + 4297778 * 2 ^ 59
def prefixEnd_4297778 : Nat := 4983230072969 + 3 ^ 40 * 4297778 * 2
def baseEnd_4297778 : Nat := 2206825860318991157509885

theorem tailTrace_4297778 : CollatzResearch.WordTrace tailWord_4297778 prefixEnd_4297778 2206825860318991157509885 := by
  unfold tailWord_4297778
  simp only [CollatzResearch.WordTrace]
  refine ⟨39188210355972945722655497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104501894282594521927081325 39188210355972945722655497)
  ·
    refine ⟨29391157766979709291991623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39188210355972945722655497 29391157766979709291991623)
    ·
      refine ⟨44086736650469563937987435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29391157766979709291991623 44086736650469563937987435)
      ·
        refine ⟨66130104975704345906981153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44086736650469563937987435 66130104975704345906981153)
        ·
          refine ⟨49597578731778259430235865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66130104975704345906981153 49597578731778259430235865)
          ·
            refine ⟨37198184048833694572676899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49597578731778259430235865 37198184048833694572676899)
            ·
              refine ⟨55797276073250541859015349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37198184048833694572676899 55797276073250541859015349)
              ·
                refine ⟨5230994631867238299282689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55797276073250541859015349 5230994631867238299282689)
                ·
                  refine ⟨3923245973900428724462017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5230994631867238299282689 3923245973900428724462017)
                  ·
                    refine ⟨2942434480425321543346513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923245973900428724462017 2942434480425321543346513)
                    ·
                      refine ⟨2206825860318991157509885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942434480425321543346513 2206825860318991157509885)
                      ·
                        rfl

theorem cell23_4297778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_4297778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297778 prefixEnd_4297778 := by exact prefixLift 4297778
  have htrace : WordTrace (prefixWord ++ tailWord_4297778) baseStart_4297778 baseEnd_4297778 := by
    simpa [prefixWord, tailWord_4297778, baseEnd_4297778] using wordTrace_append hprefix tailTrace_4297778
  have hstable : (prefixWord ++ tailWord_4297778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297778).length < 2 ^ (prefixWord ++ tailWord_4297778).sum := by decide
  have hdescent : baseEnd_4297778 < baseStart_4297778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297784 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 7]
def baseStart_4297784 : Nat := 118140960795 + 4297784 * 2 ^ 59
def prefixEnd_4297784 : Nat := 4983230072969 + 3 ^ 40 * 4297784 * 2
def baseEnd_4297784 : Nat := 245203215689213126003873

theorem tailTrace_4297784 : CollatzResearch.WordTrace tailWord_4297784 prefixEnd_4297784 245203215689213126003873 := by
  unfold tailWord_4297784
  simp only [CollatzResearch.WordTrace]
  refine ⟨78376530130935022957670203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104502040174580030610226937 78376530130935022957670203)
  ·
    refine ⟨117564795196402534436505305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78376530130935022957670203 117564795196402534436505305)
    ·
      refine ⟨88173596397301900827378979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117564795196402534436505305 88173596397301900827378979)
      ·
        refine ⟨132260394595952851241068469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88173596397301900827378979 132260394595952851241068469)
        ·
          refine ⟨12399411993370579803850169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132260394595952851241068469 12399411993370579803850169)
          ·
            refine ⟨9299558995027934852887627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12399411993370579803850169 9299558995027934852887627)
            ·
              refine ⟨13949338492541902279331441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9299558995027934852887627 13949338492541902279331441)
              ·
                refine ⟨10462003869406426709498581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13949338492541902279331441 10462003869406426709498581)
                ·
                  refine ⟨245203215689213126003873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10462003869406426709498581 245203215689213126003873)
                  ·
                    rfl

theorem cell23_4297784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_4297784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297784 prefixEnd_4297784 := by exact prefixLift 4297784
  have htrace : WordTrace (prefixWord ++ tailWord_4297784) baseStart_4297784 baseEnd_4297784 := by
    simpa [prefixWord, tailWord_4297784, baseEnd_4297784] using wordTrace_append hprefix tailTrace_4297784
  have hstable : (prefixWord ++ tailWord_4297784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297784).length < 2 ^ (prefixWord ++ tailWord_4297784).sum := by decide
  have hdescent : baseEnd_4297784 < baseStart_4297784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297904 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_4297904 : Nat := 118140960795 + 4297904 * 2 ^ 59
def prefixEnd_4297904 : Nat := 4983230072969 + 3 ^ 40 * 4297904 * 2
def baseEnd_4297904 : Nat := 735630186293819221511435

theorem tailTrace_4297904 : CollatzResearch.WordTrace tailWord_4297904 prefixEnd_4297904 735630186293819221511435 := by
  unfold tailWord_4297904
  simp only [CollatzResearch.WordTrace]
  refine ⟨78378718510717653204854383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104504958014290204273139177 78378718510717653204854383)
  ·
    refine ⟨117568077766076479807281575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78378718510717653204854383 117568077766076479807281575)
    ·
      refine ⟨176352116649114719710922363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117568077766076479807281575 176352116649114719710922363)
      ·
        refine ⟨264528174973672079566383545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176352116649114719710922363 264528174973672079566383545)
        ·
          refine ⟨198396131230254059674787659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264528174973672079566383545 198396131230254059674787659)
          ·
            refine ⟨297594196845381089512181489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198396131230254059674787659 297594196845381089512181489)
            ·
              refine ⟨223195647634035817134136117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297594196845381089512181489 223195647634035817134136117)
              ·
                refine ⟨20924591965690857856325261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223195647634035817134136117 20924591965690857856325261)
                ·
                  refine ⟨7846721987134071696121973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20924591965690857856325261 7846721987134071696121973)
                  ·
                    refine ⟨735630186293819221511435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7846721987134071696121973 735630186293819221511435)
                    ·
                      rfl

theorem cell23_4297904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_4297904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297904 prefixEnd_4297904 := by exact prefixLift 4297904
  have htrace : WordTrace (prefixWord ++ tailWord_4297904) baseStart_4297904 baseEnd_4297904 := by
    simpa [prefixWord, tailWord_4297904, baseEnd_4297904] using wordTrace_append hprefix tailTrace_4297904
  have hstable : (prefixWord ++ tailWord_4297904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297904).length < 2 ^ (prefixWord ++ tailWord_4297904).sum := by decide
  have hdescent : baseEnd_4297904 < baseStart_4297904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297928 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_4297928 : Nat := 118140960795 + 4297928 * 2 ^ 59
def prefixEnd_4297928 : Nat := 4983230072969 + 3 ^ 40 * 4297928 * 2
def baseEnd_4297928 : Nat := 2206902882417165570634195

theorem tailTrace_4297928 : CollatzResearch.WordTrace tailWord_4297928 prefixEnd_4297928 2206902882417165570634195 := by
  unfold tailWord_4297928
  simp only [CollatzResearch.WordTrace]
  refine ⟨78379156186674179254291219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104505541582232239005721625 78379156186674179254291219)
  ·
    refine ⟨117568734280011268881436829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78379156186674179254291219 117568734280011268881436829)
    ·
      refine ⟨44088275355004225830538811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117568734280011268881436829 44088275355004225830538811)
      ·
        refine ⟨66132413032506338745808217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44088275355004225830538811 66132413032506338745808217)
        ·
          refine ⟨49599309774379754059356163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66132413032506338745808217 49599309774379754059356163)
          ·
            refine ⟨74398964661569631089034245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49599309774379754059356163 74398964661569631089034245)
            ·
              refine ⟨13949805874044305829193921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74398964661569631089034245 13949805874044305829193921)
              ·
                refine ⟨10462354405533229371895441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13949805874044305829193921 10462354405533229371895441)
                ·
                  refine ⟨7846765804149922028921581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10462354405533229371895441 7846765804149922028921581)
                  ·
                    refine ⟨2942537176556220760845593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7846765804149922028921581 2942537176556220760845593)
                    ·
                      refine ⟨2206902882417165570634195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942537176556220760845593 2206902882417165570634195)
                      ·
                        rfl

theorem cell23_4297928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_4297928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297928 prefixEnd_4297928 := by exact prefixLift 4297928
  have htrace : WordTrace (prefixWord ++ tailWord_4297928) baseStart_4297928 baseEnd_4297928 := by
    simpa [prefixWord, tailWord_4297928, baseEnd_4297928] using wordTrace_append hprefix tailTrace_4297928
  have hstable : (prefixWord ++ tailWord_4297928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297928).length < 2 ^ (prefixWord ++ tailWord_4297928).sum := by decide
  have hdescent : baseEnd_4297928 < baseStart_4297928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297971 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4]
def baseStart_4297971 : Nat := 118140960795 + 4297971 * 2 ^ 59
def prefixEnd_4297971 : Nat := 4983230072969 + 3 ^ 40 * 4297971 * 2
def baseEnd_4297971 : Nat := 2206924962085308902396497

theorem tailTrace_4297971 : CollatzResearch.WordTrace tailWord_4297971 prefixEnd_4297971 2206924962085308902396497 := by
  unfold tailWord_4297971
  simp only [CollatzResearch.WordTrace]
  refine ⟨156759880712192576852397767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104506587141461717901598511 156759880712192576852397767)
  ·
    refine ⟨235139821068288865278596651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156759880712192576852397767 235139821068288865278596651)
    ·
      refine ⟨352709731602433297917894977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235139821068288865278596651 352709731602433297917894977)
      ·
        refine ⟨264532298701824973438421233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352709731602433297917894977 264532298701824973438421233)
        ·
          refine ⟨198399224026368730078815925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264532298701824973438421233 198399224026368730078815925)
          ·
            refine ⟨18599927252472068444888993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198399224026368730078815925 18599927252472068444888993)
            ·
              refine ⟨13949945439354051333666745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18599927252472068444888993 13949945439354051333666745)
              ·
                refine ⟨10462459079515538500250059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13949945439354051333666745 10462459079515538500250059)
                ·
                  refine ⟨15693688619273307750375089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10462459079515538500250059 15693688619273307750375089)
                  ·
                    refine ⟨11770266464454980812781317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15693688619273307750375089 11770266464454980812781317)
                    ·
                      refine ⟨2206924962085308902396497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11770266464454980812781317 2206924962085308902396497)
                      ·
                        rfl

theorem cell23_4297971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_4297971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297971 prefixEnd_4297971 := by exact prefixLift 4297971
  have htrace : WordTrace (prefixWord ++ tailWord_4297971) baseStart_4297971 baseEnd_4297971 := by
    simpa [prefixWord, tailWord_4297971, baseEnd_4297971] using wordTrace_append hprefix tailTrace_4297971
  have hstable : (prefixWord ++ tailWord_4297971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297971).length < 2 ^ (prefixWord ++ tailWord_4297971).sum := by decide
  have hdescent : baseEnd_4297971 < baseStart_4297971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297978 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_4297978 : Nat := 118140960795 + 4297978 * 2 ^ 59
def prefixEnd_4297978 : Nat := 4983230072969 + 3 ^ 40 * 4297978 * 2
def baseEnd_4297978 : Nat := 2206928556449890375008965

theorem tailTrace_4297978 : CollatzResearch.WordTrace tailWord_4297978 prefixEnd_4297978 2206928556449890375008965 := by
  unfold tailWord_4297978
  simp only [CollatzResearch.WordTrace]
  refine ⟨39190034005791804261975647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104506757348778144698601725 39190034005791804261975647)
  ·
    refine ⟨58785051008687706392963471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39190034005791804261975647 58785051008687706392963471)
    ·
      refine ⟨88177576513031559589445207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58785051008687706392963471 88177576513031559589445207)
      ·
        refine ⟨132266364769547339384167811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88177576513031559589445207 132266364769547339384167811)
        ·
          refine ⟨198399547154321009076251717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132266364769547339384167811 198399547154321009076251717)
          ·
            refine ⟨37199915091435189201797197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198399547154321009076251717 37199915091435189201797197)
            ·
              refine ⟨13949968159288195950673949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37199915091435189201797197 13949968159288195950673949)
              ·
                refine ⟨5231238059733073481502731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13949968159288195950673949 5231238059733073481502731)
                ·
                  refine ⟨7846857089599610222254097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231238059733073481502731 7846857089599610222254097)
                  ·
                    refine ⟨5885142817199707666690573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7846857089599610222254097 5885142817199707666690573)
                    ·
                      refine ⟨2206928556449890375008965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885142817199707666690573 2206928556449890375008965)
                      ·
                        rfl

theorem cell23_4297978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_4297978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297978 prefixEnd_4297978 := by exact prefixLift 4297978
  have htrace : WordTrace (prefixWord ++ tailWord_4297978) baseStart_4297978 baseEnd_4297978 := by
    simpa [prefixWord, tailWord_4297978, baseEnd_4297978] using wordTrace_append hprefix tailTrace_4297978
  have hstable : (prefixWord ++ tailWord_4297978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297978).length < 2 ^ (prefixWord ++ tailWord_4297978).sum := by decide
  have hdescent : baseEnd_4297978 < baseStart_4297978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297984 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_4297984 : Nat := 118140960795 + 4297984 * 2 ^ 59
def prefixEnd_4297984 : Nat := 4983230072969 + 3 ^ 40 * 4297984 * 2
def baseEnd_4297984 : Nat := 2206931637333817351533937

theorem tailTrace_4297984 : CollatzResearch.WordTrace tailWord_4297984 prefixEnd_4297984 2206931637333817351533937 := by
  unfold tailWord_4297984
  simp only [CollatzResearch.WordTrace]
  refine ⟨78380177430572740036310503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104506903240763653381747337 78380177430572740036310503)
  ·
    refine ⟨117570266145859110054465755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78380177430572740036310503 117570266145859110054465755)
    ·
      refine ⟨176355399218788665081698633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117570266145859110054465755 176355399218788665081698633)
      ·
        refine ⟨132266549414091498811273975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176355399218788665081698633 132266549414091498811273975)
        ·
          refine ⟨198399824121137248216910963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132266549414091498811273975 198399824121137248216910963)
          ·
            refine ⟨297599736181705872325366445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198399824121137248216910963 297599736181705872325366445)
            ·
              refine ⟨111599901068139702122012417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297599736181705872325366445 111599901068139702122012417)
              ·
                refine ⟨83699925801104776591509313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111599901068139702122012417 83699925801104776591509313)
                ·
                  refine ⟨62774944350828582443631985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83699925801104776591509313 62774944350828582443631985)
                  ·
                    refine ⟨47081208263121436832723989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62774944350828582443631985 47081208263121436832723989)
                    ·
                      refine ⟨2206931637333817351533937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47081208263121436832723989 2206931637333817351533937)
                      ·
                        rfl

theorem cell23_4297984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_4297984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297984 prefixEnd_4297984 := by exact prefixLift 4297984
  have htrace : WordTrace (prefixWord ++ tailWord_4297984) baseStart_4297984 baseEnd_4297984 := by
    simpa [prefixWord, tailWord_4297984, baseEnd_4297984] using wordTrace_append hprefix tailTrace_4297984
  have hstable : (prefixWord ++ tailWord_4297984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297984).length < 2 ^ (prefixWord ++ tailWord_4297984).sum := by decide
  have hdescent : baseEnd_4297984 < baseStart_4297984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297985 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4297985 : Nat := 118140960795 + 4297985 * 2 ^ 59
def prefixEnd_4297985 : Nat := 4983230072969 + 3 ^ 40 * 4297985 * 2
def baseEnd_4297985 : Nat := 735644050271490615873811

theorem tailTrace_4297985 : CollatzResearch.WordTrace tailWord_4297985 prefixEnd_4297985 735644050271490615873811 := by
  unfold tailWord_4297985
  simp only [CollatzResearch.WordTrace]
  refine ⟨156760391334141857243407409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104506927556094571495604939 156760391334141857243407409)
  ·
    refine ⟨117570293500606392932555557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156760391334141857243407409 117570293500606392932555557)
    ·
      refine ⟨22044430031363698674854167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117570293500606392932555557 22044430031363698674854167)
      ·
        refine ⟨33066645047045548012281251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22044430031363698674854167 33066645047045548012281251)
        ·
          refine ⟨49599967570568322018421877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33066645047045548012281251 49599967570568322018421877)
          ·
            refine ⟨4649996959740780189227051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49599967570568322018421877 4649996959740780189227051)
            ·
              refine ⟨6974995439611170283840577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649996959740780189227051 6974995439611170283840577)
              ·
                refine ⟨5231246579708377712880433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6974995439611170283840577 5231246579708377712880433)
                ·
                  refine ⟨3923434934781283284660325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231246579708377712880433 3923434934781283284660325)
                  ·
                    refine ⟨735644050271490615873811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923434934781283284660325 735644050271490615873811)
                    ·
                      rfl

theorem cell23_4297985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4297985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297985 prefixEnd_4297985 := by exact prefixLift 4297985
  have htrace : WordTrace (prefixWord ++ tailWord_4297985) baseStart_4297985 baseEnd_4297985 := by
    simpa [prefixWord, tailWord_4297985, baseEnd_4297985] using wordTrace_append hprefix tailTrace_4297985
  have hstable : (prefixWord ++ tailWord_4297985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297985).length < 2 ^ (prefixWord ++ tailWord_4297985).sum := by decide
  have hdescent : baseEnd_4297985 < baseStart_4297985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4297992 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_4297992 : Nat := 118140960795 + 4297992 * 2 ^ 59
def prefixEnd_4297992 : Nat := 4983230072969 + 3 ^ 40 * 4297992 * 2
def baseEnd_4297992 : Nat := 2206935745179053320233901

theorem tailTrace_4297992 : CollatzResearch.WordTrace tailWord_4297992 prefixEnd_4297992 2206935745179053320233901 := by
  unfold tailWord_4297992
  simp only [CollatzResearch.WordTrace]
  refine ⟨78380323322558248719456115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104507097763410998292608153 78380323322558248719456115)
  ·
    refine ⟨117570484983837373079184173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78380323322558248719456115 117570484983837373079184173)
    ·
      refine ⟨44088931868939014904694065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117570484983837373079184173 44088931868939014904694065)
      ·
        refine ⟨33066698901704261178520549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44088931868939014904694065 33066698901704261178520549)
        ·
          refine ⟨6200006044069548970972603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33066698901704261178520549 6200006044069548970972603)
          ·
            refine ⟨9300009066104323456458905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200006044069548970972603 9300009066104323456458905)
            ·
              refine ⟨6975006799578242592344179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9300009066104323456458905 6975006799578242592344179)
              ·
                refine ⟨10462510199367363888516269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6975006799578242592344179 10462510199367363888516269)
                ·
                  refine ⟨3923441324762761458193601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10462510199367363888516269 3923441324762761458193601)
                  ·
                    refine ⟨2942580993572071093645201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923441324762761458193601 2942580993572071093645201)
                    ·
                      refine ⟨2206935745179053320233901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942580993572071093645201 2206935745179053320233901)
                      ·
                        rfl

theorem cell23_4297992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_4297992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4297992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4297992 prefixEnd_4297992 := by exact prefixLift 4297992
  have htrace : WordTrace (prefixWord ++ tailWord_4297992) baseStart_4297992 baseEnd_4297992 := by
    simpa [prefixWord, tailWord_4297992, baseEnd_4297992] using wordTrace_append hprefix tailTrace_4297992
  have hstable : (prefixWord ++ tailWord_4297992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4297992).length < 2 ^ (prefixWord ++ tailWord_4297992).sum := by decide
  have hdescent : baseEnd_4297992 < baseStart_4297992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4297992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298002 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4298002 : Nat := 118140960795 + 4298002 * 2 ^ 59
def prefixEnd_4298002 : Nat := 4983230072969 + 3 ^ 40 * 4298002 * 2
def baseEnd_4298002 : Nat := 735646959995199427036285

theorem tailTrace_4298002 : CollatzResearch.WordTrace tailWord_4298002 prefixEnd_4298002 735646959995199427036285 := by
  unfold tailWord_4298002
  simp only [CollatzResearch.WordTrace]
  refine ⟨39190252843770067286694065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104507340916720179431184173 39190252843770067286694065)
  ·
    refine ⟨29392689632827550465020549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39190252843770067286694065 29392689632827550465020549)
    ·
      refine ⟨5511129306155165712191353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29392689632827550465020549 5511129306155165712191353)
      ·
        refine ⟨4133346979616374284143515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5511129306155165712191353 4133346979616374284143515)
        ·
          refine ⟨6200020469424561426215273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133346979616374284143515 6200020469424561426215273)
          ·
            refine ⟨4650015352068421069661455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6200020469424561426215273 4650015352068421069661455)
            ·
              refine ⟨6975023028102631604492183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650015352068421069661455 6975023028102631604492183)
              ·
                refine ⟨10462534542153947406738275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6975023028102631604492183 10462534542153947406738275)
                ·
                  refine ⟨15693801813230921110107413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10462534542153947406738275 15693801813230921110107413)
                  ·
                    refine ⟨735646959995199427036285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15693801813230921110107413 735646959995199427036285)
                    ·
                      rfl

theorem cell23_4298002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4298002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298002 prefixEnd_4298002 := by exact prefixLift 4298002
  have htrace : WordTrace (prefixWord ++ tailWord_4298002) baseStart_4298002 baseEnd_4298002 := by
    simpa [prefixWord, tailWord_4298002, baseEnd_4298002] using wordTrace_append hprefix tailTrace_4298002
  have hstable : (prefixWord ++ tailWord_4298002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298002).length < 2 ^ (prefixWord ++ tailWord_4298002).sum := by decide
  have hdescent : baseEnd_4298002 < baseStart_4298002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298008 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4298008 : Nat := 118140960795 + 4298008 * 2 ^ 59
def prefixEnd_4298008 : Nat := 4983230072969 + 3 ^ 40 * 4298008 * 2
def baseEnd_4298008 : Nat := 2206943960869525257633827

theorem tailTrace_4298008 : CollatzResearch.WordTrace tailWord_4298008 prefixEnd_4298008 2206943960869525257633827 := by
  unfold tailWord_4298008
  simp only [CollatzResearch.WordTrace]
  refine ⟨78380615106529266085747339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104507486808705688114329785 78380615106529266085747339)
  ·
    refine ⟨117570922659793899128621009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78380615106529266085747339 117570922659793899128621009)
    ·
      refine ⟨88178191994845424346465757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117570922659793899128621009 88178191994845424346465757)
      ·
        refine ⟨33066821998067034129924659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88178191994845424346465757 33066821998067034129924659)
        ·
          refine ⟨49600232997100551194886989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33066821998067034129924659 49600232997100551194886989)
          ·
            refine ⟨18600087373912706698082621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49600232997100551194886989 18600087373912706698082621)
            ·
              refine ⟨6975032765217265011780983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18600087373912706698082621 6975032765217265011780983)
              ·
                refine ⟨10462549147825897517671475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6975032765217265011780983 10462549147825897517671475)
                ·
                  refine ⟨15693823721738846276507213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10462549147825897517671475 15693823721738846276507213)
                  ·
                    refine ⟨5885183895652067353690205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15693823721738846276507213 5885183895652067353690205)
                    ·
                      refine ⟨2206943960869525257633827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885183895652067353690205 2206943960869525257633827)
                      ·
                        rfl

theorem cell23_4298008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4298008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298008 prefixEnd_4298008 := by exact prefixLift 4298008
  have htrace : WordTrace (prefixWord ++ tailWord_4298008) baseStart_4298008 baseEnd_4298008 := by
    simpa [prefixWord, tailWord_4298008, baseEnd_4298008] using wordTrace_append hprefix tailTrace_4298008
  have hstable : (prefixWord ++ tailWord_4298008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298008).length < 2 ^ (prefixWord ++ tailWord_4298008).sum := by decide
  have hdescent : baseEnd_4298008 < baseStart_4298008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298015 : List Nat := [1, 1, 2, 4, 5, 1, 2, 7]
def baseStart_4298015 : Nat := 118140960795 + 4298015 * 2 ^ 59
def prefixEnd_4298015 : Nat := 4983230072969 + 3 ^ 40 * 4298015 * 2
def baseEnd_4298015 : Nat := 81738798342003952972085

theorem tailTrace_4298015 : CollatzResearch.WordTrace tailWord_4298015 prefixEnd_4298015 81738798342003952972085 := by
  unfold tailWord_4298015
  simp only [CollatzResearch.WordTrace]
  refine ⟨156761485524033172366999499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104507657016022114911332999 156761485524033172366999499)
  ·
    refine ⟨235142228286049758550499249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156761485524033172366999499 235142228286049758550499249)
    ·
      refine ⟨176356671214537318912874437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235142228286049758550499249 176356671214537318912874437)
      ·
        refine ⟨33066875852725747296163957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176356671214537318912874437 33066875852725747296163957)
        ·
          refine ⟨3100019611193038809015371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33066875852725747296163957 3100019611193038809015371)
          ·
            refine ⟨4650029416789558213523057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100019611193038809015371 4650029416789558213523057)
            ·
              refine ⟨3487522062592168660142293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650029416789558213523057 3487522062592168660142293)
              ·
                refine ⟨81738798342003952972085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3487522062592168660142293 81738798342003952972085)
                ·
                  rfl

theorem cell23_4298015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 7].length) (baseStart_4298015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298015 prefixEnd_4298015 := by exact prefixLift 4298015
  have htrace : WordTrace (prefixWord ++ tailWord_4298015) baseStart_4298015 baseEnd_4298015 := by
    simpa [prefixWord, tailWord_4298015, baseEnd_4298015] using wordTrace_append hprefix tailTrace_4298015
  have hstable : (prefixWord ++ tailWord_4298015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298015).length < 2 ^ (prefixWord ++ tailWord_4298015).sum := by decide
  have hdescent : baseEnd_4298015 < baseStart_4298015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298021 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_4298021 : Nat := 118140960795 + 4298021 * 2 ^ 59
def prefixEnd_4298021 : Nat := 4983230072969 + 3 ^ 40 * 4298021 * 2
def baseEnd_4298021 : Nat := 2206950636118033706771267

theorem tailTrace_4298021 : CollatzResearch.WordTrace tailWord_4298021 prefixEnd_4298021 2206950636118033706771267 := by
  unfold tailWord_4298021
  simp only [CollatzResearch.WordTrace]
  refine ⟨156761704362011435391717917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104507802908007623594478611 156761704362011435391717917)
  ·
    refine ⟨58785639135754288271894219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156761704362011435391717917 58785639135754288271894219)
    ·
      refine ⟨88178458703631432407841329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58785639135754288271894219 88178458703631432407841329)
      ·
        refine ⟨66133844027723574305880997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88178458703631432407841329 66133844027723574305880997)
        ·
          refine ⟨12400095755198170182352687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66133844027723574305880997 12400095755198170182352687)
          ·
            refine ⟨18600143632797255273529031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12400095755198170182352687 18600143632797255273529031)
            ·
              refine ⟨27900215449195882910293547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18600143632797255273529031 27900215449195882910293547)
              ·
                refine ⟨41850323173793824365440321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27900215449195882910293547 41850323173793824365440321)
                ·
                  refine ⟨31387742380345368274080241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41850323173793824365440321 31387742380345368274080241)
                  ·
                    refine ⟨23540806785259026205560181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31387742380345368274080241 23540806785259026205560181)
                    ·
                      refine ⟨2206950636118033706771267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23540806785259026205560181 2206950636118033706771267)
                      ·
                        rfl

theorem cell23_4298021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_4298021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298021 prefixEnd_4298021 := by exact prefixLift 4298021
  have htrace : WordTrace (prefixWord ++ tailWord_4298021) baseStart_4298021 baseEnd_4298021 := by
    simpa [prefixWord, tailWord_4298021, baseEnd_4298021] using wordTrace_append hprefix tailTrace_4298021
  have hstable : (prefixWord ++ tailWord_4298021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298021).length < 2 ^ (prefixWord ++ tailWord_4298021).sum := by decide
  have hdescent : baseEnd_4298021 < baseStart_4298021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298026 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4298026 : Nat := 118140960795 + 4298026 * 2 ^ 59
def prefixEnd_4298026 : Nat := 4983230072969 + 3 ^ 40 * 4298026 * 2
def baseEnd_4298026 : Nat := 2206953203521306187208745

theorem tailTrace_4298026 : CollatzResearch.WordTrace tailWord_4298026 prefixEnd_4298026 2206953203521306187208745 := by
  unfold tailWord_4298026
  simp only [CollatzResearch.WordTrace]
  refine ⟨39190471681748330311412483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104507924484662214163766621 39190471681748330311412483)
  ·
    refine ⟨58785707522622495467118725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39190471681748330311412483 58785707522622495467118725)
    ·
      refine ⟨11022320160491717900084761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58785707522622495467118725 11022320160491717900084761)
      ·
        refine ⟨8266740120368788425063571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11022320160491717900084761 8266740120368788425063571)
        ·
          refine ⟨12400110180553182637595357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8266740120368788425063571 12400110180553182637595357)
          ·
            refine ⟨4650041317707443489098259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12400110180553182637595357 4650041317707443489098259)
            ·
              refine ⟨6975061976561165233647389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650041317707443489098259 6975061976561165233647389)
              ·
                refine ⟨2615648241210436962617771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6975061976561165233647389 2615648241210436962617771)
                ·
                  refine ⟨3923472361815655443926657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615648241210436962617771 3923472361815655443926657)
                  ·
                    refine ⟨2942604271361741582944993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923472361815655443926657 2942604271361741582944993)
                    ·
                      refine ⟨2206953203521306187208745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942604271361741582944993 2206953203521306187208745)
                      ·
                        rfl

theorem cell23_4298026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4298026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298026 prefixEnd_4298026 := by exact prefixLift 4298026
  have htrace : WordTrace (prefixWord ++ tailWord_4298026) baseStart_4298026 baseEnd_4298026 := by
    simpa [prefixWord, tailWord_4298026, baseEnd_4298026] using wordTrace_append hprefix tailTrace_4298026
  have hstable : (prefixWord ++ tailWord_4298026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298026).length < 2 ^ (prefixWord ++ tailWord_4298026).sum := by decide
  have hdescent : baseEnd_4298026 < baseStart_4298026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298035 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 1, 3, 2]
def baseStart_4298035 : Nat := 118140960795 + 4298035 * 2 ^ 59
def prefixEnd_4298035 : Nat := 4983230072969 + 3 ^ 40 * 4298035 * 2
def baseEnd_4298035 : Nat := 2206957824847196651996203

theorem tailTrace_4298035 : CollatzResearch.WordTrace tailWord_4298035 prefixEnd_4298035 2206957824847196651996203 := by
  unfold tailWord_4298035
  simp only [CollatzResearch.WordTrace]
  refine ⟨156762214983960715782727559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104508143322640477188485039 156762214983960715782727559)
  ·
    refine ⟨235143322475941073674091339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156762214983960715782727559 235143322475941073674091339)
    ·
      refine ⟨352714983713911610511137009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235143322475941073674091339 352714983713911610511137009)
      ·
        refine ⟨264536237785433707883352757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352714983713911610511137009 264536237785433707883352757)
        ·
          refine ⟨24800272292384410114064321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264536237785433707883352757 24800272292384410114064321)
          ·
            refine ⟨18600204219288307585548241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24800272292384410114064321 18600204219288307585548241)
            ·
              refine ⟨13950153164466230689161181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18600204219288307585548241 13950153164466230689161181)
              ·
                refine ⟨5231307436674836508435443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13950153164466230689161181 5231307436674836508435443)
                ·
                  refine ⟨7846961155012254762653165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231307436674836508435443 7846961155012254762653165)
                  ·
                    refine ⟨2942610433129595535994937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7846961155012254762653165 2942610433129595535994937)
                    ·
                      refine ⟨2206957824847196651996203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942610433129595535994937 2206957824847196651996203)
                      ·
                        rfl

theorem cell23_4298035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 3, 2].length) (baseStart_4298035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298035 prefixEnd_4298035 := by exact prefixLift 4298035
  have htrace : WordTrace (prefixWord ++ tailWord_4298035) baseStart_4298035 baseEnd_4298035 := by
    simpa [prefixWord, tailWord_4298035, baseEnd_4298035] using wordTrace_append hprefix tailTrace_4298035
  have hstable : (prefixWord ++ tailWord_4298035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298035).length < 2 ^ (prefixWord ++ tailWord_4298035).sum := by decide
  have hdescent : baseEnd_4298035 < baseStart_4298035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298051 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 3]
def baseStart_4298051 : Nat := 118140960795 + 4298051 * 2 ^ 59
def prefixEnd_4298051 : Nat := 4983230072969 + 3 ^ 40 * 4298051 * 2
def baseEnd_4298051 : Nat := 2206966040537668589396129

theorem tailTrace_4298051 : CollatzResearch.WordTrace tailWord_4298051 prefixEnd_4298051 2206966040537668589396129 := by
  unfold tailWord_4298051
  simp only [CollatzResearch.WordTrace]
  refine ⟨156762798551902750515310007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104508532367935167010206671 156762798551902750515310007)
  ·
    refine ⟨235144197827854125772965011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156762798551902750515310007 235144197827854125772965011)
    ·
      refine ⟨352716296741781188659447517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235144197827854125772965011 352716296741781188659447517)
      ·
        refine ⟨132268611278167945747292819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352716296741781188659447517 132268611278167945747292819)
        ·
          refine ⟨198402916917251918620939229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132268611278167945747292819 198402916917251918620939229)
          ·
            refine ⟨74401093843969469482852211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198402916917251918620939229 74401093843969469482852211)
            ·
              refine ⟨111601640765954204224278317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74401093843969469482852211 111601640765954204224278317)
              ·
                refine ⟨41850615287232826584104369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111601640765954204224278317 41850615287232826584104369)
                ·
                  refine ⟨31387961465424619938078277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41850615287232826584104369 31387961465424619938078277)
                  ·
                    refine ⟨5885242774767116238389677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31387961465424619938078277 5885242774767116238389677)
                    ·
                      refine ⟨2206966040537668589396129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885242774767116238389677 2206966040537668589396129)
                      ·
                        rfl

theorem cell23_4298051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_4298051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298051 prefixEnd_4298051 := by exact prefixLift 4298051
  have htrace : WordTrace (prefixWord ++ tailWord_4298051) baseStart_4298051 baseEnd_4298051 := by
    simpa [prefixWord, tailWord_4298051, baseEnd_4298051] using wordTrace_append hprefix tailTrace_4298051
  have hstable : (prefixWord ++ tailWord_4298051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298051).length < 2 ^ (prefixWord ++ tailWord_4298051).sum := by decide
  have hdescent : baseEnd_4298051 < baseStart_4298051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298098 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4298098 : Nat := 118140960795 + 4298098 * 2 ^ 59
def prefixEnd_4298098 : Nat := 4983230072969 + 3 ^ 40 * 4298098 * 2
def baseEnd_4298098 : Nat := 2206990174128429905508413

theorem tailTrace_4298098 : CollatzResearch.WordTrace tailWord_4298098 prefixEnd_4298098 2206990174128429905508413 := by
  unfold tailWord_4298098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39191128195683119385567737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104509675188488318361513965 39191128195683119385567737)
  ·
    refine ⟨29393346146762339539175803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39191128195683119385567737 29393346146762339539175803)
    ·
      refine ⟨44090019220143509308763705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29393346146762339539175803 44090019220143509308763705)
      ·
        refine ⟨33067514415107631981572779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44090019220143509308763705 33067514415107631981572779)
        ·
          refine ⟨49601271622661447972359169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33067514415107631981572779 49601271622661447972359169)
          ·
            refine ⟨37200953716996085979269377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49601271622661447972359169 37200953716996085979269377)
            ·
              refine ⟨27900715287747064484452033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37200953716996085979269377 27900715287747064484452033)
              ·
                refine ⟨20925536465810298363339025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27900715287747064484452033 20925536465810298363339025)
                ·
                  refine ⟨15694152349357723772504269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20925536465810298363339025 15694152349357723772504269)
                  ·
                    refine ⟨5885307131009146414689101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15694152349357723772504269 5885307131009146414689101)
                    ·
                      refine ⟨2206990174128429905508413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885307131009146414689101 2206990174128429905508413)
                      ·
                        rfl

theorem cell23_4298098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4298098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298098 prefixEnd_4298098 := by exact prefixLift 4298098
  have htrace : WordTrace (prefixWord ++ tailWord_4298098) baseStart_4298098 baseEnd_4298098 := by
    simpa [prefixWord, tailWord_4298098, baseEnd_4298098] using wordTrace_append hprefix tailTrace_4298098
  have hstable : (prefixWord ++ tailWord_4298098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298098).length < 2 ^ (prefixWord ++ tailWord_4298098).sum := by decide
  have hdescent : baseEnd_4298098 < baseStart_4298098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298105 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 5]
def baseStart_4298105 : Nat := 118140960795 + 4298105 * 2 ^ 59
def prefixEnd_4298105 : Nat := 4983230072969 + 3 ^ 40 * 4298105 * 2
def baseEnd_4298105 : Nat := 245221529832556819791209

theorem tailTrace_4298105 : CollatzResearch.WordTrace tailWord_4298105 prefixEnd_4298105 245221529832556819791209 := by
  unfold tailWord_4298105
  simp only [CollatzResearch.WordTrace]
  refine ⟨156764768093707117737775769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104509845395804745158517179 156764768093707117737775769)
  ·
    refine ⟨117573576070280338303331827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156764768093707117737775769 117573576070280338303331827)
    ·
      refine ⟨176360364105420507454997741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117573576070280338303331827 176360364105420507454997741)
      ·
        refine ⟨66135136539532690295624153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176360364105420507454997741 66135136539532690295624153)
        ·
          refine ⟨49601352404649517721718115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66135136539532690295624153 49601352404649517721718115)
          ·
            refine ⟨74402028606974276582577173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49601352404649517721718115 74402028606974276582577173)
            ·
              refine ⟨3487595090951919214808305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74402028606974276582577173 3487595090951919214808305)
              ·
                refine ⟨2615696318213939411106229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3487595090951919214808305 2615696318213939411106229)
                ·
                  refine ⟨245221529832556819791209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2615696318213939411106229 245221529832556819791209)
                  ·
                    rfl

theorem cell23_4298105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 5].length) (baseStart_4298105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298105 prefixEnd_4298105 := by exact prefixLift 4298105
  have htrace : WordTrace (prefixWord ++ tailWord_4298105) baseStart_4298105 baseEnd_4298105 := by
    simpa [prefixWord, tailWord_4298105, baseEnd_4298105] using wordTrace_append hprefix tailTrace_4298105
  have hstable : (prefixWord ++ tailWord_4298105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298105).length < 2 ^ (prefixWord ++ tailWord_4298105).sum := by decide
  have hdescent : baseEnd_4298105 < baseStart_4298105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298108 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_4298108 : Nat := 118140960795 + 4298108 * 2 ^ 59
def prefixEnd_4298108 : Nat := 4983230072969 + 3 ^ 40 * 4298108 * 2
def baseEnd_4298108 : Nat := 2206995308934974866383367

theorem tailTrace_4298108 : CollatzResearch.WordTrace tailWord_4298108 prefixEnd_4298108 2206995308934974866383367 := by
  unfold tailWord_4298108
  simp only [CollatzResearch.WordTrace]
  refine ⟨78382438756348124625067489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104509918341797499500089985 78382438756348124625067489)
  ·
    refine ⟨58786829067261093468800617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78382438756348124625067489 58786829067261093468800617)
    ·
      refine ⟨44090121800445820101600463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58786829067261093468800617 44090121800445820101600463)
      ·
        refine ⟨66135182700668730152400695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44090121800445820101600463 66135182700668730152400695)
        ·
          refine ⟨99202774051003095228601043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66135182700668730152400695 99202774051003095228601043)
          ·
            refine ⟨148804161076504642842901565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99202774051003095228601043 148804161076504642842901565)
            ·
              refine ⟨55801560403689241066088087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148804161076504642842901565 55801560403689241066088087)
              ·
                refine ⟨83702340605533861599132131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55801560403689241066088087 83702340605533861599132131)
                ·
                  refine ⟨125553510908300792398698197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83702340605533861599132131 125553510908300792398698197)
                  ·
                    refine ⟨2942660411913299821844489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 125553510908300792398698197 2942660411913299821844489)
                    ·
                      refine ⟨2206995308934974866383367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942660411913299821844489 2206995308934974866383367)
                      ·
                        rfl

theorem cell23_4298108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_4298108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298108 prefixEnd_4298108 := by exact prefixLift 4298108
  have htrace : WordTrace (prefixWord ++ tailWord_4298108) baseStart_4298108 baseEnd_4298108 := by
    simpa [prefixWord, tailWord_4298108, baseEnd_4298108] using wordTrace_append hprefix tailTrace_4298108
  have hstable : (prefixWord ++ tailWord_4298108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298108).length < 2 ^ (prefixWord ++ tailWord_4298108).sum := by decide
  have hdescent : baseEnd_4298108 < baseStart_4298108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298138 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4298138 : Nat := 118140960795 + 4298138 * 2 ^ 59
def prefixEnd_4298138 : Nat := 4983230072969 + 3 ^ 40 * 4298138 * 2
def baseEnd_4298138 : Nat := 2207010713354609749008229

theorem tailTrace_4298138 : CollatzResearch.WordTrace tailWord_4298138 prefixEnd_4298138 2207010713354609749008229 := by
  unfold tailWord_4298138
  simp only [CollatzResearch.WordTrace]
  refine ⟨39191492925646891093431767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104510647801725042915818045 39191492925646891093431767)
  ·
    refine ⟨58787239388470336640147651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39191492925646891093431767 58787239388470336640147651)
    ·
      refine ⟨88180859082705504960221477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58787239388470336640147651 88180859082705504960221477)
      ·
        refine ⟨16533911078007282180041527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88180859082705504960221477 16533911078007282180041527)
        ·
          refine ⟨24800866617010923270062291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16533911078007282180041527 24800866617010923270062291)
          ·
            refine ⟨37201299925516384905093437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24800866617010923270062291 37201299925516384905093437)
            ·
              refine ⟨13950487472068644339410039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37201299925516384905093437 13950487472068644339410039)
              ·
                refine ⟨20925731208102966509115059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13950487472068644339410039 20925731208102966509115059)
                ·
                  refine ⟨31388596812154449763672589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20925731208102966509115059 31388596812154449763672589)
                  ·
                    refine ⟨11770723804557918661377221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31388596812154449763672589 11770723804557918661377221)
                    ·
                      refine ⟨2207010713354609749008229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11770723804557918661377221 2207010713354609749008229)
                      ·
                        rfl

theorem cell23_4298138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4298138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298138 prefixEnd_4298138 := by exact prefixLift 4298138
  have htrace : WordTrace (prefixWord ++ tailWord_4298138) baseStart_4298138 baseEnd_4298138 := by
    simpa [prefixWord, tailWord_4298138, baseEnd_4298138] using wordTrace_append hprefix tailTrace_4298138
  have hstable : (prefixWord ++ tailWord_4298138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298138).length < 2 ^ (prefixWord ++ tailWord_4298138).sum := by decide
  have hdescent : baseEnd_4298138 < baseStart_4298138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298148 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_4298148 : Nat := 118140960795 + 4298148 * 2 ^ 59
def prefixEnd_4298148 : Nat := 4983230072969 + 3 ^ 40 * 4298148 * 2
def baseEnd_4298148 : Nat := 735671949387051569961061

theorem tailTrace_4298148 : CollatzResearch.WordTrace tailWord_4298148 prefixEnd_4298148 735671949387051569961061 := by
  unfold tailWord_4298148
  simp only [CollatzResearch.WordTrace]
  refine ⟨78383168216275668040795549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104510890955034224054394065 78383168216275668040795549)
  ·
    refine ⟨29393688081103375515298331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78383168216275668040795549 29393688081103375515298331)
    ·
      refine ⟨44090532121655063272947497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29393688081103375515298331 44090532121655063272947497)
      ·
        refine ⟨33067899091241297454710623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44090532121655063272947497 33067899091241297454710623)
        ·
          refine ⟨49601848636861946182065935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33067899091241297454710623 49601848636861946182065935)
          ·
            refine ⟨74402772955292919273098903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49601848636861946182065935 74402772955292919273098903)
            ·
              refine ⟨111604159432939378909648355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74402772955292919273098903 111604159432939378909648355)
              ·
                refine ⟨167406239149409068364472533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111604159432939378909648355 167406239149409068364472533)
                ·
                  refine ⟨3923583730064275039792325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 167406239149409068364472533 3923583730064275039792325)
                  ·
                    refine ⟨735671949387051569961061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923583730064275039792325 735671949387051569961061)
                    ·
                      rfl

theorem cell23_4298148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_4298148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298148 prefixEnd_4298148 := by exact prefixLift 4298148
  have htrace : WordTrace (prefixWord ++ tailWord_4298148) baseStart_4298148 baseEnd_4298148 := by
    simpa [prefixWord, tailWord_4298148, baseEnd_4298148] using wordTrace_append hprefix tailTrace_4298148
  have hstable : (prefixWord ++ tailWord_4298148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298148).length < 2 ^ (prefixWord ++ tailWord_4298148).sum := by decide
  have hdescent : baseEnd_4298148 < baseStart_4298148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298165 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_4298165 : Nat := 118140960795 + 4298165 * 2 ^ 59
def prefixEnd_4298165 : Nat := 4983230072969 + 3 ^ 40 * 4298165 * 2
def baseEnd_4298165 : Nat := 735674859110760381123535

theorem tailTrace_4298165 : CollatzResearch.WordTrace tailWord_4298165 prefixEnd_4298165 735674859110760381123535 := by
  unfold tailWord_4298165
  simp only [CollatzResearch.WordTrace]
  refine ⟨156766956473489747984959949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104511304315659831989973299 156766956473489747984959949)
  ·
    refine ⟨58787608677558655494359981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156766956473489747984959949 58787608677558655494359981)
    ·
      refine ⟨22045353254084495810384993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58787608677558655494359981 22045353254084495810384993)
      ·
        refine ⟨16534014940563371857788745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22045353254084495810384993 16534014940563371857788745)
        ·
          refine ⟨12400511205422528893341559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16534014940563371857788745 12400511205422528893341559)
          ·
            refine ⟨18600766808133793340012339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12400511205422528893341559 18600766808133793340012339)
            ·
              refine ⟨27901150212200690010018509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18600766808133793340012339 27901150212200690010018509)
              ·
                refine ⟨10462931329575258753756941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27901150212200690010018509 10462931329575258753756941)
                ·
                  refine ⟨3923599248590722032658853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10462931329575258753756941 3923599248590722032658853)
                  ·
                    refine ⟨735674859110760381123535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923599248590722032658853 735674859110760381123535)
                    ·
                      rfl

theorem cell23_4298165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_4298165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298165 prefixEnd_4298165 := by exact prefixLift 4298165
  have htrace : WordTrace (prefixWord ++ tailWord_4298165) baseStart_4298165 baseEnd_4298165 := by
    simpa [prefixWord, tailWord_4298165, baseEnd_4298165] using wordTrace_append hprefix tailTrace_4298165
  have hstable : (prefixWord ++ tailWord_4298165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298165).length < 2 ^ (prefixWord ++ tailWord_4298165).sum := by decide
  have hdescent : baseEnd_4298165 < baseStart_4298165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298229 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 6]
def baseStart_4298229 : Nat := 118140960795 + 4298229 * 2 ^ 59
def prefixEnd_4298229 : Nat := 4983230072969 + 3 ^ 40 * 4298229 * 2
def baseEnd_4298229 : Nat := 245228604454907654774479

theorem tailTrace_4298229 : CollatzResearch.WordTrace tailWord_4298229 prefixEnd_4298229 245228604454907654774479 := by
  unfold tailWord_4298229
  simp only [CollatzResearch.WordTrace]
  refine ⟨156769290745257886915289741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104512860496838591276859827 156769290745257886915289741)
  ·
    refine ⟨58788484029471707593233653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156769290745257886915289741 58788484029471707593233653)
    ·
      refine ⟨5511420377762972586865655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58788484029471707593233653 5511420377762972586865655)
      ·
        refine ⟨8267130566644458880298483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5511420377762972586865655 8267130566644458880298483)
        ·
          refine ⟨12400695849966688320447725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8267130566644458880298483 12400695849966688320447725)
          ·
            refine ⟨4650260943737508120167897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12400695849966688320447725 4650260943737508120167897)
            ·
              refine ⟨3487695707803131090125923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650260943737508120167897 3487695707803131090125923)
              ·
                refine ⟨5231543561704696635188885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487695707803131090125923 5231543561704696635188885)
                ·
                  refine ⟨245228604454907654774479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5231543561704696635188885 245228604454907654774479)
                  ·
                    rfl

theorem cell23_4298229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_4298229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298229 prefixEnd_4298229 := by exact prefixLift 4298229
  have htrace : WordTrace (prefixWord ++ tailWord_4298229) baseStart_4298229 baseEnd_4298229 := by
    simpa [prefixWord, tailWord_4298229, baseEnd_4298229] using wordTrace_append hprefix tailTrace_4298229
  have hstable : (prefixWord ++ tailWord_4298229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298229).length < 2 ^ (prefixWord ++ tailWord_4298229).sum := by decide
  have hdescent : baseEnd_4298229 < baseStart_4298229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298242 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4298242 : Nat := 118140960795 + 4298242 * 2 ^ 59
def prefixEnd_4298242 : Nat := 4983230072969 + 3 ^ 40 * 4298242 * 2
def baseEnd_4298242 : Nat := 735688038447559114035917

theorem tailTrace_4298242 : CollatzResearch.WordTrace tailWord_4298242 prefixEnd_4298242 735688038447559114035917 := by
  unfold tailWord_4298242
  simp only [CollatzResearch.WordTrace]
  refine ⟨39192441223552697533878245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104513176596140526757008653 39192441223552697533878245)
  ·
    refine ⟨7348582729416130787602171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39192441223552697533878245 7348582729416130787602171)
    ·
      refine ⟨11022874094124196181403257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7348582729416130787602171 11022874094124196181403257)
      ·
        refine ⟨8267155570593147136052443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11022874094124196181403257 8267155570593147136052443)
        ·
          refine ⟨12400733355889720704078665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8267155570593147136052443 12400733355889720704078665)
          ·
            refine ⟨9300550016917290528058999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12400733355889720704078665 9300550016917290528058999)
            ·
              refine ⟨13950825025375935792088499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9300550016917290528058999 13950825025375935792088499)
              ·
                refine ⟨20926237538063903688132749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13950825025375935792088499 20926237538063903688132749)
                ·
                  refine ⟨7847339076773963883049781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20926237538063903688132749 7847339076773963883049781)
                  ·
                    refine ⟨735688038447559114035917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7847339076773963883049781 735688038447559114035917)
                    ·
                      rfl

theorem cell23_4298242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4298242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298242 prefixEnd_4298242 := by exact prefixLift 4298242
  have htrace : WordTrace (prefixWord ++ tailWord_4298242) baseStart_4298242 baseEnd_4298242 := by
    simpa [prefixWord, tailWord_4298242, baseEnd_4298242] using wordTrace_append hprefix tailTrace_4298242
  have hstable : (prefixWord ++ tailWord_4298242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298242).length < 2 ^ (prefixWord ++ tailWord_4298242).sum := by decide
  have hdescent : baseEnd_4298242 < baseStart_4298242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298248 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_4298248 : Nat := 118140960795 + 4298248 * 2 ^ 59
def prefixEnd_4298248 : Nat := 4983230072969 + 3 ^ 40 * 4298248 * 2
def baseEnd_4298248 : Nat := 2207067196226604318632723

theorem tailTrace_4298248 : CollatzResearch.WordTrace tailWord_4298248 prefixEnd_4298248 2207067196226604318632723 := by
  unfold tailWord_4298248
  simp only [CollatzResearch.WordTrace]
  refine ⟨78384991866094526580115699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104513322488126035440154265 78384991866094526580115699)
  ·
    refine ⟨117577487799141789870173549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78384991866094526580115699 117577487799141789870173549)
    ·
      refine ⟨44091557924678171201315081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117577487799141789870173549 44091557924678171201315081)
      ·
        refine ⟨33068668443508628400986311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44091557924678171201315081 33068668443508628400986311)
        ·
          refine ⟨49603002665262942601479467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33068668443508628400986311 49603002665262942601479467)
          ·
            refine ⟨74404503997894413902219201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49603002665262942601479467 74404503997894413902219201)
            ·
              refine ⟨55803377998420810426664401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74404503997894413902219201 55803377998420810426664401)
              ·
                refine ⟨41852533498815607819998301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55803377998420810426664401 41852533498815607819998301)
                ·
                  refine ⟨15694700062055852932499363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41852533498815607819998301 15694700062055852932499363)
                  ·
                    refine ⟨23542050093083779398749045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15694700062055852932499363 23542050093083779398749045)
                    ·
                      refine ⟨2207067196226604318632723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23542050093083779398749045 2207067196226604318632723)
                      ·
                        rfl

theorem cell23_4298248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_4298248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298248 prefixEnd_4298248 := by exact prefixLift 4298248
  have htrace : WordTrace (prefixWord ++ tailWord_4298248) baseStart_4298248 baseEnd_4298248 := by
    simpa [prefixWord, tailWord_4298248, baseEnd_4298248] using wordTrace_append hprefix tailTrace_4298248
  have hstable : (prefixWord ++ tailWord_4298248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298248).length < 2 ^ (prefixWord ++ tailWord_4298248).sum := by decide
  have hdescent : baseEnd_4298248 < baseStart_4298248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298272 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 2, 4]
def baseStart_4298272 : Nat := 118140960795 + 4298272 * 2 ^ 59
def prefixEnd_4298272 : Nat := 4983230072969 + 3 ^ 40 * 4298272 * 2
def baseEnd_4298272 : Nat := 735693173254104074910871

theorem tailTrace_4298272 : CollatzResearch.WordTrace tailWord_4298272 prefixEnd_4298272 735693173254104074910871 := by
  unfold tailWord_4298272
  simp only [CollatzResearch.WordTrace]
  refine ⟨78385429542051052629552535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104513906056068070172736713 78385429542051052629552535)
  ·
    refine ⟨117578144313076578944328803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78385429542051052629552535 117578144313076578944328803)
    ·
      refine ⟨176367216469614868416493205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117578144313076578944328803 176367216469614868416493205)
      ·
        refine ⟨8267213272013196957023119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 176367216469614868416493205 8267213272013196957023119)
        ·
          refine ⟨12400819908019795435534679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8267213272013196957023119 12400819908019795435534679)
          ·
            refine ⟨18601229862029693153302019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12400819908019795435534679 18601229862029693153302019)
            ·
              refine ⟨27901844793044539729953029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18601229862029693153302019 27901844793044539729953029)
              ·
                refine ⟨5231595898695851199366193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27901844793044539729953029 5231595898695851199366193)
                ·
                  refine ⟨3923696924021888399524645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231595898695851199366193 3923696924021888399524645)
                  ·
                    refine ⟨735693173254104074910871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923696924021888399524645 735693173254104074910871)
                    ·
                      rfl

theorem cell23_4298272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_4298272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298272 prefixEnd_4298272 := by exact prefixLift 4298272
  have htrace : WordTrace (prefixWord ++ tailWord_4298272) baseStart_4298272 baseEnd_4298272 := by
    simpa [prefixWord, tailWord_4298272, baseEnd_4298272] using wordTrace_append hprefix tailTrace_4298272
  have hstable : (prefixWord ++ tailWord_4298272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298272).length < 2 ^ (prefixWord ++ tailWord_4298272).sum := by decide
  have hdescent : baseEnd_4298272 < baseStart_4298272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298295 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_4298295 : Nat := 118140960795 + 4298295 * 2 ^ 59
def prefixEnd_4298295 : Nat := 4983230072969 + 3 ^ 40 * 4298295 * 2
def baseEnd_4298295 : Nat := 2207091329817365634745007

theorem tailTrace_4298295 : CollatzResearch.WordTrace tailWord_4298295 prefixEnd_4298295 2207091329817365634745007 := by
  unfold tailWord_4298295
  simp only [CollatzResearch.WordTrace]
  refine ⟨156771697963018780187192339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104514465308679186791461559 156771697963018780187192339)
  ·
    refine ⟨235157546944528170280788509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156771697963018780187192339 235157546944528170280788509)
    ·
      refine ⟨88184080104198063855295691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235157546944528170280788509 88184080104198063855295691)
      ·
        refine ⟨132276120156297095782943537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88184080104198063855295691 132276120156297095782943537)
        ·
          refine ⟨99207090117222821837207653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132276120156297095782943537 99207090117222821837207653)
          ·
            refine ⟨18601329396979279094476435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99207090117222821837207653 18601329396979279094476435)
            ·
              refine ⟨27901994095468918641714653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18601329396979279094476435 27901994095468918641714653)
              ·
                refine ⟨10463247785800844490642995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27901994095468918641714653 10463247785800844490642995)
                ·
                  refine ⟨15694871678701266735964493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10463247785800844490642995 15694871678701266735964493)
                  ·
                    refine ⟨5885576879512975025986685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15694871678701266735964493 5885576879512975025986685)
                    ·
                      refine ⟨2207091329817365634745007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885576879512975025986685 2207091329817365634745007)
                      ·
                        rfl

theorem cell23_4298295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_4298295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298295 prefixEnd_4298295 := by exact prefixLift 4298295
  have htrace : WordTrace (prefixWord ++ tailWord_4298295) baseStart_4298295 baseEnd_4298295 := by
    simpa [prefixWord, tailWord_4298295, baseEnd_4298295] using wordTrace_append hprefix tailTrace_4298295
  have hstable : (prefixWord ++ tailWord_4298295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298295).length < 2 ^ (prefixWord ++ tailWord_4298295).sum := by decide
  have hdescent : baseEnd_4298295 < baseStart_4298295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298298 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_4298298 : Nat := 118140960795 + 4298298 * 2 ^ 59
def prefixEnd_4298298 : Nat := 4983230072969 + 3 ^ 40 * 4298298 * 2
def baseEnd_4298298 : Nat := 735697623419776374335831

theorem tailTrace_4298298 : CollatzResearch.WordTrace tailWord_4298298 prefixEnd_4298298 735697623419776374335831 := by
  unfold tailWord_4298298
  simp only [CollatzResearch.WordTrace]
  refine ⟨39192951845501977924887887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104514538254671941133034365 39192951845501977924887887)
  ·
    refine ⟨58789427768252966887331831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39192951845501977924887887 58789427768252966887331831)
    ·
      refine ⟨88184141652379450330997747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58789427768252966887331831 88184141652379450330997747)
      ·
        refine ⟨132276212478569175496496621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88184141652379450330997747 132276212478569175496496621)
        ·
          refine ⟨49603579679463440811186233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132276212478569175496496621 49603579679463440811186233)
          ·
            refine ⟨37202684759597580608389675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49603579679463440811186233 37202684759597580608389675)
            ·
              refine ⟨55804027139396370912584513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37202684759597580608389675 55804027139396370912584513)
              ·
                refine ⟨41853020354547278184438385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55804027139396370912584513 41853020354547278184438385)
                ·
                  refine ⟨31389765265910458638328789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41853020354547278184438385 31389765265910458638328789)
                  ·
                    refine ⟨735697623419776374335831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31389765265910458638328789 735697623419776374335831)
                    ·
                      rfl

theorem cell23_4298298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_4298298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298298 prefixEnd_4298298 := by exact prefixLift 4298298
  have htrace : WordTrace (prefixWord ++ tailWord_4298298) baseStart_4298298 baseEnd_4298298 := by
    simpa [prefixWord, tailWord_4298298, baseEnd_4298298] using wordTrace_append hprefix tailTrace_4298298
  have hstable : (prefixWord ++ tailWord_4298298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298298).length < 2 ^ (prefixWord ++ tailWord_4298298).sum := by decide
  have hdescent : baseEnd_4298298 < baseStart_4298298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298335 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 8, 2]
def baseStart_4298335 : Nat := 118140960795 + 4298335 * 2 ^ 59
def prefixEnd_4298335 : Nat := 4983230072969 + 3 ^ 40 * 4298335 * 2
def baseEnd_4298335 : Nat := 2207111869043545478244823

theorem tailTrace_4298335 : CollatzResearch.WordTrace tailWord_4298335 prefixEnd_4298335 2207111869043545478244823 := by
  unfold tailWord_4298335
  simp only [CollatzResearch.WordTrace]
  refine ⟨156773156882873867018648459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104515437921915911345765639 156773156882873867018648459)
  ·
    refine ⟨235159735324310800527972689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156773156882873867018648459 235159735324310800527972689)
    ·
      refine ⟨176369801493233100395979517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235159735324310800527972689 176369801493233100395979517)
      ·
        refine ⟨66138675559962412648492319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176369801493233100395979517 66138675559962412648492319)
        ·
          refine ⟨99208013339943618972738479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66138675559962412648492319 99208013339943618972738479)
          ·
            refine ⟨148812020009915428459107719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99208013339943618972738479 148812020009915428459107719)
            ·
              refine ⟨223218030014873142688661579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148812020009915428459107719 223218030014873142688661579)
              ·
                refine ⟨334827045022309714032992369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223218030014873142688661579 334827045022309714032992369)
                ·
                  refine ⟨251120283766732285524744277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334827045022309714032992369 251120283766732285524744277)
                  ·
                    refine ⟨2942815825391393970993097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 251120283766732285524744277 2942815825391393970993097)
                    ·
                      refine ⟨2207111869043545478244823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942815825391393970993097 2207111869043545478244823)
                      ·
                        rfl

theorem cell23_4298335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_4298335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298335 prefixEnd_4298335 := by exact prefixLift 4298335
  have htrace : WordTrace (prefixWord ++ tailWord_4298335) baseStart_4298335 baseEnd_4298335 := by
    simpa [prefixWord, tailWord_4298335, baseEnd_4298335] using wordTrace_append hprefix tailTrace_4298335
  have hstable : (prefixWord ++ tailWord_4298335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298335).length < 2 ^ (prefixWord ++ tailWord_4298335).sum := by decide
  have hdescent : baseEnd_4298335 < baseStart_4298335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298346 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_4298346 : Nat := 118140960795 + 4298346 * 2 ^ 59
def prefixEnd_4298346 : Nat := 4983230072969 + 3 ^ 40 * 4298346 * 2
def baseEnd_4298346 : Nat := 2207117517330744935207273

theorem tailTrace_4298346 : CollatzResearch.WordTrace tailWord_4298346 prefixEnd_4298346 2207117517330744935207273 := by
  unfold tailWord_4298346
  simp only [CollatzResearch.WordTrace]
  refine ⟨39193389521458503974324723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104515705390556010598199261 39193389521458503974324723)
  ·
    refine ⟨58790084282187755961487085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39193389521458503974324723 58790084282187755961487085)
    ·
      refine ⟨22046281605820408485557657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58790084282187755961487085 22046281605820408485557657)
      ·
        refine ⟨16534711204365306364168243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22046281605820408485557657 16534711204365306364168243)
        ·
          refine ⟨24802066806547959546252365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16534711204365306364168243 24802066806547959546252365)
          ·
            refine ⟨9300775052455484829844637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24802066806547959546252365 9300775052455484829844637)
            ·
              refine ⟨3487790644670806811191739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9300775052455484829844637 3487790644670806811191739)
              ·
                refine ⟨5231685967006210216787609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487790644670806811191739 5231685967006210216787609)
                ·
                  refine ⟨3923764475254657662590707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231685967006210216787609 3923764475254657662590707)
                  ·
                    refine ⟨5885646712881986493886061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3923764475254657662590707 5885646712881986493886061)
                    ·
                      refine ⟨2207117517330744935207273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885646712881986493886061 2207117517330744935207273)
                      ·
                        rfl

theorem cell23_4298346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_4298346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298346 prefixEnd_4298346 := by exact prefixLift 4298346
  have htrace : WordTrace (prefixWord ++ tailWord_4298346) baseStart_4298346 baseEnd_4298346 := by
    simpa [prefixWord, tailWord_4298346, baseEnd_4298346] using wordTrace_append hprefix tailTrace_4298346
  have hstable : (prefixWord ++ tailWord_4298346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298346).length < 2 ^ (prefixWord ++ tailWord_4298346).sum := by decide
  have hdescent : baseEnd_4298346 < baseStart_4298346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298369 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_4298369 : Nat := 118140960795 + 4298369 * 2 ^ 59
def prefixEnd_4298369 : Nat := 4983230072969 + 3 ^ 40 * 4298369 * 2
def baseEnd_4298369 : Nat := 2207129327385798345219667

theorem tailTrace_4298369 : CollatzResearch.WordTrace tailWord_4298369 prefixEnd_4298369 2207129327385798345219667 := by
  unfold tailWord_4298369
  simp only [CollatzResearch.WordTrace]
  refine ⟨156774396964750690825386161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104516264643167127216924107 156774396964750690825386161)
  ·
    refine ⟨117580797723563018119039621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156774396964750690825386161 117580797723563018119039621)
    ·
      refine ⟨22046399573168065897319929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117580797723563018119039621 22046399573168065897319929)
      ·
        refine ⟨16534799679876049422989947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22046399573168065897319929 16534799679876049422989947)
        ·
          refine ⟨24802199519814074134484921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16534799679876049422989947 24802199519814074134484921)
          ·
            refine ⟨18601649639860555600863691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24802199519814074134484921 18601649639860555600863691)
            ·
              refine ⟨27902474459790833401295537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18601649639860555600863691 27902474459790833401295537)
              ·
                refine ⟨20926855844843125050971653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27902474459790833401295537 20926855844843125050971653)
                ·
                  refine ⟨3923785470908085947057185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20926855844843125050971653 3923785470908085947057185)
                  ·
                    refine ⟨2942839103181064460292889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923785470908085947057185 2942839103181064460292889)
                    ·
                      refine ⟨2207129327385798345219667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942839103181064460292889 2207129327385798345219667)
                      ·
                        rfl

theorem cell23_4298369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_4298369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298369 prefixEnd_4298369 := by exact prefixLift 4298369
  have htrace : WordTrace (prefixWord ++ tailWord_4298369) baseStart_4298369 baseEnd_4298369 := by
    simpa [prefixWord, tailWord_4298369, baseEnd_4298369] using wordTrace_append hprefix tailTrace_4298369
  have hstable : (prefixWord ++ tailWord_4298369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298369).length < 2 ^ (prefixWord ++ tailWord_4298369).sum := by decide
  have hdescent : baseEnd_4298369 < baseStart_4298369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298372 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_4298372 : Nat := 118140960795 + 4298372 * 2 ^ 59
def prefixEnd_4298372 : Nat := 4983230072969 + 3 ^ 40 * 4298372 * 2
def baseEnd_4298372 : Nat := 2207130867827761833482153

theorem tailTrace_4298372 : CollatzResearch.WordTrace tailWord_4298372 prefixEnd_4298372 2207130867827761833482153 := by
  unfold tailWord_4298372
  simp only [CollatzResearch.WordTrace]
  refine ⟨78387253191869911168872685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104516337589159881558496913 78387253191869911168872685)
  ·
    refine ⟨29395219946951216688327257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78387253191869911168872685 29395219946951216688327257)
    ·
      refine ⟨22046414960213412516245443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29395219946951216688327257 22046414960213412516245443)
      ·
        refine ⟨33069622440320118774368165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22046414960213412516245443 33069622440320118774368165)
        ·
          refine ⟨6200554207560022270194031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33069622440320118774368165 6200554207560022270194031)
          ·
            refine ⟨9300831311340033405291047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200554207560022270194031 9300831311340033405291047)
            ·
              refine ⟨13951246967010050107936571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9300831311340033405291047 13951246967010050107936571)
              ·
                refine ⟨20926870450515075161904857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13951246967010050107936571 20926870450515075161904857)
                ·
                  refine ⟨15695152837886306371428643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20926870450515075161904857 15695152837886306371428643)
                  ·
                    refine ⟨23542729256829459557142965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15695152837886306371428643 23542729256829459557142965)
                    ·
                      refine ⟨2207130867827761833482153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23542729256829459557142965 2207130867827761833482153)
                      ·
                        rfl

theorem cell23_4298372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_4298372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298372 prefixEnd_4298372 := by exact prefixLift 4298372
  have htrace : WordTrace (prefixWord ++ tailWord_4298372) baseStart_4298372 baseEnd_4298372 := by
    simpa [prefixWord, tailWord_4298372, baseEnd_4298372] using wordTrace_append hprefix tailTrace_4298372
  have hstable : (prefixWord ++ tailWord_4298372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298372).length < 2 ^ (prefixWord ++ tailWord_4298372).sum := by decide
  have hdescent : baseEnd_4298372 < baseStart_4298372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298385 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_4298385 : Nat := 118140960795 + 4298385 * 2 ^ 59
def prefixEnd_4298385 : Nat := 4983230072969 + 3 ^ 40 * 4298385 * 2
def baseEnd_4298385 : Nat := 2207137543076270282619593

theorem tailTrace_4298385 : CollatzResearch.WordTrace tailWord_4298385 prefixEnd_4298385 2207137543076270282619593 := by
  unfold tailWord_4298385
  simp only [CollatzResearch.WordTrace]
  refine ⟨156774980532692725557968609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104516653688461817038645739 156774980532692725557968609)
  ·
    refine ⟨117581235399519544168476457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156774980532692725557968609 117581235399519544168476457)
    ·
      refine ⟨88185926549639658126357343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117581235399519544168476457 88185926549639658126357343)
      ·
        refine ⟨132278889824459487189536015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88185926549639658126357343 132278889824459487189536015)
        ·
          refine ⟨198418334736689230784304023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132278889824459487189536015 198418334736689230784304023)
          ·
            refine ⟨297627502105033846176456035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198418334736689230784304023 297627502105033846176456035)
            ·
              refine ⟨446441253157550769264684053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297627502105033846176456035 446441253157550769264684053)
              ·
                refine ⟨20926933741760192309282065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 446441253157550769264684053 20926933741760192309282065)
                ·
                  refine ⟨15695200306320144231961549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20926933741760192309282065 15695200306320144231961549)
                  ·
                    refine ⟨5885700114870054086985581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15695200306320144231961549 5885700114870054086985581)
                    ·
                      refine ⟨2207137543076270282619593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885700114870054086985581 2207137543076270282619593)
                      ·
                        rfl

theorem cell23_4298385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_4298385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298385 prefixEnd_4298385 := by exact prefixLift 4298385
  have htrace : WordTrace (prefixWord ++ tailWord_4298385) baseStart_4298385 baseEnd_4298385 := by
    simpa [prefixWord, tailWord_4298385, baseEnd_4298385] using wordTrace_append hprefix tailTrace_4298385
  have hstable : (prefixWord ++ tailWord_4298385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298385).length < 2 ^ (prefixWord ++ tailWord_4298385).sum := by decide
  have hdescent : baseEnd_4298385 < baseStart_4298385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298392 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 7]
def baseStart_4298392 : Nat := 118140960795 + 4298392 * 2 ^ 59
def prefixEnd_4298392 : Nat := 4983230072969 + 3 ^ 40 * 4298392 * 2
def baseEnd_4298392 : Nat := 245237904160094639470229

theorem tailTrace_4298392 : CollatzResearch.WordTrace tailWord_4298392 prefixEnd_4298392 245237904160094639470229 := by
  unfold tailWord_4298392
  simp only [CollatzResearch.WordTrace]
  refine ⟨78387617921833682876736715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104516823895778243835648953 78387617921833682876736715)
  ·
    refine ⟨117581426882750524315105073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78387617921833682876736715 117581426882750524315105073)
    ·
      refine ⟨88186070162062893236328805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117581426882750524315105073 88186070162062893236328805)
      ·
        refine ⟨16534888155386792481811651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88186070162062893236328805 16534888155386792481811651)
        ·
          refine ⟨24802332233080188722717477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16534888155386792481811651 24802332233080188722717477)
          ·
            refine ⟨4650437293702535385509527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24802332233080188722717477 4650437293702535385509527)
            ·
              refine ⟨6975655940553803078264291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650437293702535385509527 6975655940553803078264291)
              ·
                refine ⟨10463483910830704617396437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6975655940553803078264291 10463483910830704617396437)
                ·
                  refine ⟨245237904160094639470229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10463483910830704617396437 245237904160094639470229)
                  ·
                    rfl

theorem cell23_4298392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 7].length) (baseStart_4298392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298392 prefixEnd_4298392 := by exact prefixLift 4298392
  have htrace : WordTrace (prefixWord ++ tailWord_4298392) baseStart_4298392 baseEnd_4298392 := by
    simpa [prefixWord, tailWord_4298392, baseEnd_4298392] using wordTrace_append hprefix tailTrace_4298392
  have hstable : (prefixWord ++ tailWord_4298392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298392).length < 2 ^ (prefixWord ++ tailWord_4298392).sum := by decide
  have hdescent : baseEnd_4298392 < baseStart_4298392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298425 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4298425 : Nat := 118140960795 + 4298425 * 2 ^ 59
def prefixEnd_4298425 : Nat := 4983230072969 + 3 ^ 40 * 4298425 * 2
def baseEnd_4298425 : Nat := 2207158082302450126119409

theorem tailTrace_4298425 : CollatzResearch.WordTrace tailWord_4298425 prefixEnd_4298425 2207158082302450126119409 := by
  unfold tailWord_4298425
  simp only [CollatzResearch.WordTrace]
  refine ⟨156776439452547812389424729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104517626301698541592949819 156776439452547812389424729)
  ·
    refine ⟨117582329589410859292068547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156776439452547812389424729 117582329589410859292068547)
    ·
      refine ⟨176373494384116288938102821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117582329589410859292068547 176373494384116288938102821)
      ·
        refine ⟨33070030197021804175894279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176373494384116288938102821 33070030197021804175894279)
        ·
          refine ⟨49605045295532706263841419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33070030197021804175894279 49605045295532706263841419)
          ·
            refine ⟨74407567943299059395762129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49605045295532706263841419 74407567943299059395762129)
            ·
              refine ⟨55805675957474294546821597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74407567943299059395762129 55805675957474294546821597)
              ·
                refine ⟨20927128484052860455058099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55805675957474294546821597 20927128484052860455058099)
                ·
                  refine ⟨31390692726079290682587149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20927128484052860455058099 31390692726079290682587149)
                  ·
                    refine ⟨11771509772279734005970181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31390692726079290682587149 11771509772279734005970181)
                    ·
                      refine ⟨2207158082302450126119409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11771509772279734005970181 2207158082302450126119409)
                      ·
                        rfl

theorem cell23_4298425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4298425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298425 prefixEnd_4298425 := by exact prefixLift 4298425
  have htrace : WordTrace (prefixWord ++ tailWord_4298425) baseStart_4298425 baseEnd_4298425 := by
    simpa [prefixWord, tailWord_4298425, baseEnd_4298425] using wordTrace_append hprefix tailTrace_4298425
  have hstable : (prefixWord ++ tailWord_4298425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298425).length < 2 ^ (prefixWord ++ tailWord_4298425).sum := by decide
  have hdescent : baseEnd_4298425 < baseStart_4298425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298486 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_4298486 : Nat := 118140960795 + 4298486 * 2 ^ 59
def prefixEnd_4298486 : Nat := 4983230072969 + 3 ^ 40 * 4298486 * 2
def baseEnd_4298486 : Nat := 735729801540791462485543

theorem tailTrace_4298486 : CollatzResearch.WordTrace tailWord_4298486 prefixEnd_4298486 735729801540791462485543 := by
  unfold tailWord_4298486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798666519082926237962207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104519109536884546538263541 9798666519082926237962207)
  ·
    refine ⟨14697999778624389356943311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9798666519082926237962207 14697999778624389356943311)
    ·
      refine ⟨22046999667936584035414967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14697999778624389356943311 22046999667936584035414967)
      ·
        refine ⟨33070499501904876053122451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22046999667936584035414967 33070499501904876053122451)
        ·
          refine ⟨49605749252857314079683677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33070499501904876053122451 49605749252857314079683677)
          ·
            refine ⟨18602155969821492779881379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49605749252857314079683677 18602155969821492779881379)
            ·
              refine ⟨27903233954732239169822069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18602155969821492779881379 27903233954732239169822069)
              ·
                refine ⟨2615928183256147422170819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27903233954732239169822069 2615928183256147422170819)
                ·
                  refine ⟨3923892274884221133256229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615928183256147422170819 3923892274884221133256229)
                  ·
                    refine ⟨735729801540791462485543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923892274884221133256229 735729801540791462485543)
                    ·
                      rfl

theorem cell23_4298486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_4298486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298486 prefixEnd_4298486 := by exact prefixLift 4298486
  have htrace : WordTrace (prefixWord ++ tailWord_4298486) baseStart_4298486 baseEnd_4298486 := by
    simpa [prefixWord, tailWord_4298486, baseEnd_4298486] using wordTrace_append hprefix tailTrace_4298486
  have hstable : (prefixWord ++ tailWord_4298486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298486).length < 2 ^ (prefixWord ++ tailWord_4298486).sum := by decide
  have hdescent : baseEnd_4298486 < baseStart_4298486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298515 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4]
def baseStart_4298515 : Nat := 118140960795 + 4298515 * 2 ^ 59
def prefixEnd_4298515 : Nat := 4983230072969 + 3 ^ 40 * 4298515 * 2
def baseEnd_4298515 : Nat := 2207204295561354773993995

theorem tailTrace_4298515 : CollatzResearch.WordTrace tailWord_4298515 prefixEnd_4298515 2207204295561354773993995 := by
  unfold tailWord_4298515
  simp only [CollatzResearch.WordTrace]
  refine ⟨156779722022221757760200999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104519814681481171840133999 156779722022221757760200999)
  ·
    refine ⟨235169583033332636640301499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156779722022221757760200999 235169583033332636640301499)
    ·
      refine ⟨352754374549998954960452249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235169583033332636640301499 352754374549998954960452249)
      ·
        refine ⟨264565780912499216220339187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352754374549998954960452249 264565780912499216220339187)
        ·
          refine ⟨396848671368748824330508781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264565780912499216220339187 396848671368748824330508781)
          ·
            refine ⟨148818251763280809123940793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396848671368748824330508781 148818251763280809123940793)
            ·
              refine ⟨111613688822460606842955595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148818251763280809123940793 111613688822460606842955595)
              ·
                refine ⟨167420533233690910264433393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111613688822460606842955595 167420533233690910264433393)
                ·
                  refine ⟨125565399925268182698325045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167420533233690910264433393 125565399925268182698325045)
                  ·
                    refine ⟨11771756242993892127967973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125565399925268182698325045 11771756242993892127967973)
                    ·
                      refine ⟨2207204295561354773993995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11771756242993892127967973 2207204295561354773993995)
                      ·
                        rfl

theorem cell23_4298515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_4298515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298515 prefixEnd_4298515 := by exact prefixLift 4298515
  have htrace : WordTrace (prefixWord ++ tailWord_4298515) baseStart_4298515 baseEnd_4298515 := by
    simpa [prefixWord, tailWord_4298515, baseEnd_4298515] using wordTrace_append hprefix tailTrace_4298515
  have hstable : (prefixWord ++ tailWord_4298515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298515).length < 2 ^ (prefixWord ++ tailWord_4298515).sum := by decide
  have hdescent : baseEnd_4298515 < baseStart_4298515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298519 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 1, 5, 2]
def baseStart_4298519 : Nat := 118140960795 + 4298519 * 2 ^ 59
def prefixEnd_4298519 : Nat := 4983230072969 + 3 ^ 40 * 4298519 * 2
def baseEnd_4298519 : Nat := 2207206349483972758343977

theorem tailTrace_4298519 : CollatzResearch.WordTrace tailWord_4298519 prefixEnd_4298519 2207206349483972758343977 := by
  unfold tailWord_4298519
  simp only [CollatzResearch.WordTrace]
  refine ⟨156779867914207266443346611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104519911942804844295564407 156779867914207266443346611)
  ·
    refine ⟨235169801871310899665019917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156779867914207266443346611 235169801871310899665019917)
    ·
      refine ⟨88188675701741587374382469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235169801871310899665019917 88188675701741587374382469)
      ·
        refine ⟨16535376694076547632696713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88188675701741587374382469 16535376694076547632696713)
        ·
          refine ⟨12401532520557410724522535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16535376694076547632696713 12401532520557410724522535)
          ·
            refine ⟨18602298780836116086783803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12401532520557410724522535 18602298780836116086783803)
            ·
              refine ⟨27903448171254174130175705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18602298780836116086783803 27903448171254174130175705)
              ·
                refine ⟨20927586128440630597631779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27903448171254174130175705 20927586128440630597631779)
                ·
                  refine ⟨31391379192660945896447669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20927586128440630597631779 31391379192660945896447669)
                  ·
                    refine ⟨2942941799311963677791969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31391379192660945896447669 2942941799311963677791969)
                    ·
                      refine ⟨2207206349483972758343977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942941799311963677791969 2207206349483972758343977)
                      ·
                        rfl

theorem cell23_4298519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_4298519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298519 prefixEnd_4298519 := by exact prefixLift 4298519
  have htrace : WordTrace (prefixWord ++ tailWord_4298519) baseStart_4298519 baseEnd_4298519 := by
    simpa [prefixWord, tailWord_4298519, baseEnd_4298519] using wordTrace_append hprefix tailTrace_4298519
  have hstable : (prefixWord ++ tailWord_4298519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298519).length < 2 ^ (prefixWord ++ tailWord_4298519).sum := by decide
  have hdescent : baseEnd_4298519 < baseStart_4298519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298529 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 1, 5]
def baseStart_4298529 : Nat := 118140960795 + 4298529 * 2 ^ 59
def prefixEnd_4298529 : Nat := 4983230072969 + 3 ^ 40 * 4298529 * 2
def baseEnd_4298529 : Nat := 735737161430172573072977

theorem tailTrace_4298529 : CollatzResearch.WordTrace tailWord_4298529 prefixEnd_4298529 735737161430172573072977 := by
  unfold tailWord_4298529
  simp only [CollatzResearch.WordTrace]
  refine ⟨156780232644171038151210641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104520155096114025434140427 156780232644171038151210641)
  ·
    refine ⟨117585174483128278613407981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156780232644171038151210641 117585174483128278613407981)
    ·
      refine ⟨44094440431173104480027993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117585174483128278613407981 44094440431173104480027993)
      ·
        refine ⟨33070830323379828360020995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44094440431173104480027993 33070830323379828360020995)
        ·
          refine ⟨49606245485069742540031493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33070830323379828360020995 49606245485069742540031493)
          ·
            refine ⟨9301171028450576726255905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49606245485069742540031493 9301171028450576726255905)
            ·
              refine ⟨6975878271337932544691929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9301171028450576726255905 6975878271337932544691929)
              ·
                refine ⟨5231908703503449408518947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6975878271337932544691929 5231908703503449408518947)
                ·
                  refine ⟨7847863055255174112778421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231908703503449408518947 7847863055255174112778421)
                  ·
                    refine ⟨735737161430172573072977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7847863055255174112778421 735737161430172573072977)
                    ·
                      rfl

theorem cell23_4298529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_4298529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298529 prefixEnd_4298529 := by exact prefixLift 4298529
  have htrace : WordTrace (prefixWord ++ tailWord_4298529) baseStart_4298529 baseEnd_4298529 := by
    simpa [prefixWord, tailWord_4298529, baseEnd_4298529] using wordTrace_append hprefix tailTrace_4298529
  have hstable : (prefixWord ++ tailWord_4298529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298529).length < 2 ^ (prefixWord ++ tailWord_4298529).sum := by decide
  have hdescent : baseEnd_4298529 < baseStart_4298529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298552 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_4298552 : Nat := 118140960795 + 4298552 * 2 ^ 59
def prefixEnd_4298552 : Nat := 4983230072969 + 3 ^ 40 * 4298552 * 2
def baseEnd_4298552 : Nat := 2207223294345571129231325

theorem tailTrace_4298552 : CollatzResearch.WordTrace tailWord_4298552 prefixEnd_4298552 2207223294345571129231325 := by
  unfold tailWord_4298552
  simp only [CollatzResearch.WordTrace]
  refine ⟨78390535761543856539648955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104520714348725142052865273 78390535761543856539648955)
  ·
    refine ⟨117585803642315784809473433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78390535761543856539648955 117585803642315784809473433)
    ·
      refine ⟨88189352731736838607105075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117585803642315784809473433 88189352731736838607105075)
      ·
        refine ⟨132284029097605257910657613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88189352731736838607105075 132284029097605257910657613)
        ·
          refine ⟨49606510911601971716496605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132284029097605257910657613 49606510911601971716496605)
          ·
            refine ⟨18602441591850739393686227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49606510911601971716496605 18602441591850739393686227)
            ·
              refine ⟨27903662387776109090529341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18602441591850739393686227 27903662387776109090529341)
              ·
                refine ⟨10463873395416040908948503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27903662387776109090529341 10463873395416040908948503)
                ·
                  refine ⟨15695810093124061363422755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10463873395416040908948503 15695810093124061363422755)
                  ·
                    refine ⟨23543715139686092045134133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15695810093124061363422755 23543715139686092045134133)
                    ·
                      refine ⟨2207223294345571129231325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23543715139686092045134133 2207223294345571129231325)
                      ·
                        rfl

theorem cell23_4298552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_4298552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298552 prefixEnd_4298552 := by exact prefixLift 4298552
  have htrace : WordTrace (prefixWord ++ tailWord_4298552) baseStart_4298552 baseEnd_4298552 := by
    simpa [prefixWord, tailWord_4298552, baseEnd_4298552] using wordTrace_append hprefix tailTrace_4298552
  have hstable : (prefixWord ++ tailWord_4298552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298552).length < 2 ^ (prefixWord ++ tailWord_4298552).sum := by decide
  have hdescent : baseEnd_4298552 < baseStart_4298552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298553 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4298553 : Nat := 118140960795 + 4298553 * 2 ^ 59
def prefixEnd_4298553 : Nat := 4983230072969 + 3 ^ 40 * 4298553 * 2
def baseEnd_4298553 : Nat := 2207223807826225625318821

theorem tailTrace_4298553 : CollatzResearch.WordTrace tailWord_4298553 prefixEnd_4298553 2207223807826225625318821 := by
  unfold tailWord_4298553
  simp only [CollatzResearch.WordTrace]
  refine ⟨156781107996084090250084313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104520738664056060166722875 156781107996084090250084313)
  ·
    refine ⟨117585830997063067687563235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156781107996084090250084313 117585830997063067687563235)
    ·
      refine ⟨176378746495594601531344853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117585830997063067687563235 176378746495594601531344853)
      ·
        refine ⟨4133876870990498473390895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 176378746495594601531344853 4133876870990498473390895)
        ·
          refine ⟨6200815306485747710086343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133876870990498473390895 6200815306485747710086343)
          ·
            refine ⟨9301222959728621565129515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200815306485747710086343 9301222959728621565129515)
            ·
              refine ⟨13951834439592932347694273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301222959728621565129515 13951834439592932347694273)
              ·
                refine ⟨10463875829694699260770705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13951834439592932347694273 10463875829694699260770705)
                ·
                  refine ⟨7847906872271024445578029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10463875829694699260770705 7847906872271024445578029)
                  ·
                    refine ⟨2942965077101634167091761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7847906872271024445578029 2942965077101634167091761)
                    ·
                      refine ⟨2207223807826225625318821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2942965077101634167091761 2207223807826225625318821)
                      ·
                        rfl

theorem cell23_4298553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4298553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298553 prefixEnd_4298553 := by exact prefixLift 4298553
  have htrace : WordTrace (prefixWord ++ tailWord_4298553) baseStart_4298553 baseEnd_4298553 := by
    simpa [prefixWord, tailWord_4298553, baseEnd_4298553] using wordTrace_append hprefix tailTrace_4298553
  have hstable : (prefixWord ++ tailWord_4298553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298553).length < 2 ^ (prefixWord ++ tailWord_4298553).sum := by decide
  have hdescent : baseEnd_4298553 < baseStart_4298553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298583 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 1, 1, 4]
def baseStart_4298583 : Nat := 118140960795 + 4298583 * 2 ^ 59
def prefixEnd_4298583 : Nat := 4983230072969 + 3 ^ 40 * 4298583 * 2
def baseEnd_4298583 : Nat := 2207239212245860507943683

theorem tailTrace_4298583 : CollatzResearch.WordTrace tailWord_4298583 prefixEnd_4298583 2207239212245860507943683 := by
  unfold tailWord_4298583
  simp only [CollatzResearch.WordTrace]
  refine ⟨156782202185975405373676403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104521468123983603582450935 156782202185975405373676403)
  ·
    refine ⟨235173303278963108060514605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156782202185975405373676403 235173303278963108060514605)
    ·
      refine ⟨88189988729611165522692977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235173303278963108060514605 88189988729611165522692977)
      ·
        refine ⟨66142491547208374142019733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88189988729611165522692977 66142491547208374142019733)
        ·
          refine ⟨3100429291275392537907175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66142491547208374142019733 3100429291275392537907175)
          ·
            refine ⟨4650643936913088806860763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100429291275392537907175 4650643936913088806860763)
            ·
              refine ⟨6975965905369633210291145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650643936913088806860763 6975965905369633210291145)
              ·
                refine ⟨5231974429027224907718359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6975965905369633210291145 5231974429027224907718359)
                ·
                  refine ⟨7847961643540837361577539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231974429027224907718359 7847961643540837361577539)
                  ·
                    refine ⟨11771942465311256042366309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7847961643540837361577539 11771942465311256042366309)
                    ·
                      refine ⟨2207239212245860507943683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11771942465311256042366309 2207239212245860507943683)
                      ·
                        rfl

theorem cell23_4298583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_4298583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298583 prefixEnd_4298583 := by exact prefixLift 4298583
  have htrace : WordTrace (prefixWord ++ tailWord_4298583) baseStart_4298583 baseEnd_4298583 := by
    simpa [prefixWord, tailWord_4298583, baseEnd_4298583] using wordTrace_append hprefix tailTrace_4298583
  have hstable : (prefixWord ++ tailWord_4298583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298583).length < 2 ^ (prefixWord ++ tailWord_4298583).sum := by decide
  have hdescent : baseEnd_4298583 < baseStart_4298583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298599 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_4298599 : Nat := 118140960795 + 4298599 * 2 ^ 59
def prefixEnd_4298599 : Nat := 4983230072969 + 3 ^ 40 * 4298599 * 2
def baseEnd_4298599 : Nat := 2207247427936332445343609

theorem tailTrace_4298599 : CollatzResearch.WordTrace tailWord_4298599 prefixEnd_4298599 2207247427936332445343609 := by
  unfold tailWord_4298599
  simp only [CollatzResearch.WordTrace]
  refine ⟨156782785753917440106258851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104521857169278293404172567 156782785753917440106258851)
  ·
    refine ⟨235174178630876160159388277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156782785753917440106258851 235174178630876160159388277)
    ·
      refine ⟨22047579246644640014942651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235174178630876160159388277 22047579246644640014942651)
      ·
        refine ⟨33071368869966960022413977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22047579246644640014942651 33071368869966960022413977)
        ·
          refine ⟨24803526652475220016810483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33071368869966960022413977 24803526652475220016810483)
          ·
            refine ⟨37205289978712830025215725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24803526652475220016810483 37205289978712830025215725)
            ·
              refine ⟨13951983742017311259455897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37205289978712830025215725 13951983742017311259455897)
              ·
                refine ⟨10463987806512983444591923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13951983742017311259455897 10463987806512983444591923)
                ·
                  refine ⟨15695981709769475166887885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10463987806512983444591923 15695981709769475166887885)
                  ·
                    refine ⟨5885993141163553187582957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15695981709769475166887885 5885993141163553187582957)
                    ·
                      refine ⟨2207247427936332445343609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5885993141163553187582957 2207247427936332445343609)
                      ·
                        rfl

theorem cell23_4298599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_4298599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298599 prefixEnd_4298599 := by exact prefixLift 4298599
  have htrace : WordTrace (prefixWord ++ tailWord_4298599) baseStart_4298599 baseEnd_4298599 := by
    simpa [prefixWord, tailWord_4298599, baseEnd_4298599] using wordTrace_append hprefix tailTrace_4298599
  have hstable : (prefixWord ++ tailWord_4298599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298599).length < 2 ^ (prefixWord ++ tailWord_4298599).sum := by decide
  have hdescent : baseEnd_4298599 < baseStart_4298599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298654 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4298654 : Nat := 118140960795 + 4298654 * 2 ^ 59
def prefixEnd_4298654 : Nat := 4983230072969 + 3 ^ 40 * 4298654 * 2
def baseEnd_4298654 : Nat := 2207275669372329730155857

theorem tailTrace_4298654 : CollatzResearch.WordTrace tailWord_4298654 prefixEnd_4298654 2207275669372329730155857 := by
  unfold tailWord_4298654
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598098971089773062438877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104523194512478789666340677 19598098971089773062438877)
  ·
    refine ⟨7349287114158664898414579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19598098971089773062438877 7349287114158664898414579)
    ·
      refine ⟨11023930671237997347621869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7349287114158664898414579 11023930671237997347621869)
      ·
        refine ⟨4133974001714249005358201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11023930671237997347621869 4133974001714249005358201)
        ·
          refine ⟨3100480501285686754018651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4133974001714249005358201 3100480501285686754018651)
          ·
            refine ⟨4650720751928530131027977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100480501285686754018651 4650720751928530131027977)
            ·
              refine ⟨3488040563946397598270983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650720751928530131027977 3488040563946397598270983)
              ·
                refine ⟨5232060845919596397406475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488040563946397598270983 5232060845919596397406475)
                ·
                  refine ⟨7848091268879394596109713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5232060845919596397406475 7848091268879394596109713)
                  ·
                    refine ⟨5886068451659545947082285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7848091268879394596109713 5886068451659545947082285)
                    ·
                      refine ⟨2207275669372329730155857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886068451659545947082285 2207275669372329730155857)
                      ·
                        rfl

theorem cell23_4298654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4298654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298654 prefixEnd_4298654 := by exact prefixLift 4298654
  have htrace : WordTrace (prefixWord ++ tailWord_4298654) baseStart_4298654 baseEnd_4298654 := by
    simpa [prefixWord, tailWord_4298654, baseEnd_4298654] using wordTrace_append hprefix tailTrace_4298654
  have hstable : (prefixWord ++ tailWord_4298654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298654).length < 2 ^ (prefixWord ++ tailWord_4298654).sum := by decide
  have hdescent : baseEnd_4298654 < baseStart_4298654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298656 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 4, 2, 2]
def baseStart_4298656 : Nat := 118140960795 + 4298656 * 2 ^ 59
def prefixEnd_4298656 : Nat := 4983230072969 + 3 ^ 40 * 4298656 * 2
def baseEnd_4298656 : Nat := 2207276696333638722330847

theorem tailTrace_4298656 : CollatzResearch.WordTrace tailWord_4298656 prefixEnd_4298656 2207276696333638722330847 := by
  unfold tailWord_4298656
  simp only [CollatzResearch.WordTrace]
  refine ⟨78392432357355469420541911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104523243143140625894055881 78392432357355469420541911)
  ·
    refine ⟨117588648536033204130812867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78392432357355469420541911 117588648536033204130812867)
    ·
      refine ⟨176382972804049806196219301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117588648536033204130812867 176382972804049806196219301)
      ·
        refine ⟨33071807400759338661791119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176382972804049806196219301 33071807400759338661791119)
        ·
          refine ⟨49607711101139007992686679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33071807400759338661791119 49607711101139007992686679)
          ·
            refine ⟨74411566651708511989030019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49607711101139007992686679 74411566651708511989030019)
            ·
              refine ⟨111617349977562767983545029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74411566651708511989030019 111617349977562767983545029)
              ·
                refine ⟨20928253120793018996914693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111617349977562767983545029 20928253120793018996914693)
                ·
                  refine ⟨3924047460148691061921505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20928253120793018996914693 3924047460148691061921505)
                  ·
                    refine ⟨2943035595111518296441129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3924047460148691061921505 2943035595111518296441129)
                    ·
                      refine ⟨2207276696333638722330847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943035595111518296441129 2207276696333638722330847)
                      ·
                        rfl

theorem cell23_4298656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_4298656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298656 prefixEnd_4298656 := by exact prefixLift 4298656
  have htrace : WordTrace (prefixWord ++ tailWord_4298656) baseStart_4298656 baseEnd_4298656 := by
    simpa [prefixWord, tailWord_4298656, baseEnd_4298656] using wordTrace_append hprefix tailTrace_4298656
  have hstable : (prefixWord ++ tailWord_4298656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298656).length < 2 ^ (prefixWord ++ tailWord_4298656).sum := by decide
  have hdescent : baseEnd_4298656 < baseStart_4298656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298660 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_4298660 : Nat := 118140960795 + 4298660 * 2 ^ 59
def prefixEnd_4298660 : Nat := 4983230072969 + 3 ^ 40 * 4298660 * 2
def baseEnd_4298660 : Nat := 2207278750256256706680829

theorem tailTrace_4298660 : CollatzResearch.WordTrace tailWord_4298660 prefixEnd_4298660 2207278750256256706680829 := by
  unfold tailWord_4298660
  simp only [CollatzResearch.WordTrace]
  refine ⟨78392505303348223762114717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104523340404464298349486289 78392505303348223762114717)
  ·
    refine ⟨29397189488755583910793019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78392505303348223762114717 29397189488755583910793019)
    ·
      refine ⟨44095784233133375866189529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29397189488755583910793019 44095784233133375866189529)
      ·
        refine ⟨33071838174850031899642147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44095784233133375866189529 33071838174850031899642147)
        ·
          refine ⟨49607757262275047849463221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33071838174850031899642147 49607757262275047849463221)
          ·
            refine ⟨4650727243338285735887177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49607757262275047849463221 4650727243338285735887177)
            ·
              refine ⟨3488045432503714301915383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650727243338285735887177 3488045432503714301915383)
              ·
                refine ⟨5232068148755571452873075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488045432503714301915383 5232068148755571452873075)
                ·
                  refine ⟨7848102223133357179309613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5232068148755571452873075 7848102223133357179309613)
                  ·
                    refine ⟨2943038333675008942241105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7848102223133357179309613 2943038333675008942241105)
                    ·
                      refine ⟨2207278750256256706680829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943038333675008942241105 2207278750256256706680829)
                      ·
                        rfl

theorem cell23_4298660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_4298660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298660 prefixEnd_4298660 := by exact prefixLift 4298660
  have htrace : WordTrace (prefixWord ++ tailWord_4298660) baseStart_4298660 baseEnd_4298660 := by
    simpa [prefixWord, tailWord_4298660, baseEnd_4298660] using wordTrace_append hprefix tailTrace_4298660
  have hstable : (prefixWord ++ tailWord_4298660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298660).length < 2 ^ (prefixWord ++ tailWord_4298660).sum := by decide
  have hdescent : baseEnd_4298660 < baseStart_4298660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298673 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 4, 2, 2]
def baseStart_4298673 : Nat := 118140960795 + 4298673 * 2 ^ 59
def prefixEnd_4298673 : Nat := 4983230072969 + 3 ^ 40 * 4298673 * 2
def baseEnd_4298673 : Nat := 2207285425504765155818269

theorem tailTrace_4298673 : CollatzResearch.WordTrace tailWord_4298673 prefixEnd_4298673 2207285425504765155818269 := by
  unfold tailWord_4298673
  simp only [CollatzResearch.WordTrace]
  refine ⟨156785484755649350744452673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104523656503766233829635115 156785484755649350744452673)
  ·
    refine ⟨117589113566737013058339505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156785484755649350744452673 117589113566737013058339505)
    ·
      refine ⟨88191835175052759793754629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117589113566737013058339505 88191835175052759793754629)
      ·
        refine ⟨16535969095322392461328993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88191835175052759793754629 16535969095322392461328993)
        ·
          refine ⟨12401976821491794345996745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16535969095322392461328993 12401976821491794345996745)
          ·
            refine ⟨9301482616118845759497559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12401976821491794345996745 9301482616118845759497559)
            ·
              refine ⟨13952223924178268639246339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301482616118845759497559 13952223924178268639246339)
              ·
                refine ⟨20928335886267402958869509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13952223924178268639246339 20928335886267402958869509)
                ·
                  refine ⟨3924062978675138054788033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20928335886267402958869509 3924062978675138054788033)
                  ·
                    refine ⟨2943047234006353541091025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3924062978675138054788033 2943047234006353541091025)
                    ·
                      refine ⟨2207285425504765155818269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943047234006353541091025 2207285425504765155818269)
                      ·
                        rfl

theorem cell23_4298673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_4298673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298673 prefixEnd_4298673 := by exact prefixLift 4298673
  have htrace : WordTrace (prefixWord ++ tailWord_4298673) baseStart_4298673 baseEnd_4298673 := by
    simpa [prefixWord, tailWord_4298673, baseEnd_4298673] using wordTrace_append hprefix tailTrace_4298673
  have hstable : (prefixWord ++ tailWord_4298673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298673).length < 2 ^ (prefixWord ++ tailWord_4298673).sum := by decide
  have hdescent : baseEnd_4298673 < baseStart_4298673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298709 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_4298709 : Nat := 118140960795 + 4298709 * 2 ^ 59
def prefixEnd_4298709 : Nat := 4983230072969 + 3 ^ 40 * 4298709 * 2
def baseEnd_4298709 : Nat := 735767970269442338322701

theorem tailTrace_4298709 : CollatzResearch.WordTrace tailWord_4298709 prefixEnd_4298709 735767970269442338322701 := by
  unfold tailWord_4298709
  simp only [CollatzResearch.WordTrace]
  refine ⟨156786797783518928892763181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104524531855679285928508787 156786797783518928892763181)
  ·
    refine ⟨58795049168819598334786193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156786797783518928892763181 58795049168819598334786193)
    ·
      refine ⟨44096286876614698751089645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58795049168819598334786193 44096286876614698751089645)
      ·
        refine ⟨16536107578730512031658617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44096286876614698751089645 16536107578730512031658617)
        ·
          refine ⟨12402080684047884023743963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16536107578730512031658617 12402080684047884023743963)
          ·
            refine ⟨18603121026071826035615945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12402080684047884023743963 18603121026071826035615945)
            ·
              refine ⟨13952340769553869526711959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18603121026071826035615945 13952340769553869526711959)
              ·
                refine ⟨20928511154330804290067939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13952340769553869526711959 20928511154330804290067939)
                ·
                  refine ⟨31392766731496206435101909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20928511154330804290067939 31392766731496206435101909)
                  ·
                    refine ⟨735767970269442338322701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31392766731496206435101909 735767970269442338322701)
                    ·
                      rfl

theorem cell23_4298709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_4298709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298709 prefixEnd_4298709 := by exact prefixLift 4298709
  have htrace : WordTrace (prefixWord ++ tailWord_4298709) baseStart_4298709 baseEnd_4298709 := by
    simpa [prefixWord, tailWord_4298709, baseEnd_4298709] using wordTrace_append hprefix tailTrace_4298709
  have hstable : (prefixWord ++ tailWord_4298709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298709).length < 2 ^ (prefixWord ++ tailWord_4298709).sum := by decide
  have hdescent : baseEnd_4298709 < baseStart_4298709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298713 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 5]
def baseStart_4298713 : Nat := 118140960795 + 4298713 * 2 ^ 59
def prefixEnd_4298713 : Nat := 4983230072969 + 3 ^ 40 * 4298713 * 2
def baseEnd_4298713 : Nat := 245256218303438333257565

theorem tailTrace_4298713 : CollatzResearch.WordTrace tailWord_4298713 prefixEnd_4298713 245256218303438333257565 := by
  unfold tailWord_4298713
  simp only [CollatzResearch.WordTrace]
  refine ⟨156786943675504437575908793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104524629117002958383939195 156786943675504437575908793)
  ·
    refine ⟨117590207756628328181931595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156786943675504437575908793 117590207756628328181931595)
    ·
      refine ⟨176385311634942492272897393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117590207756628328181931595 176385311634942492272897393)
      ·
        refine ⟨132288983726206869204673045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176385311634942492272897393 132288983726206869204673045)
        ·
          refine ⟨6201046112165946993969049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132288983726206869204673045 6201046112165946993969049)
          ·
            refine ⟨4650784584124460245476787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6201046112165946993969049 4650784584124460245476787)
            ·
              refine ⟨6976176876186690368215181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650784584124460245476787 6976176876186690368215181)
              ·
                refine ⟨2616066328570008888080693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6976176876186690368215181 2616066328570008888080693)
                ·
                  refine ⟨245256218303438333257565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2616066328570008888080693 245256218303438333257565)
                  ·
                    rfl

theorem cell23_4298713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 5].length) (baseStart_4298713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298713 prefixEnd_4298713 := by exact prefixLift 4298713
  have htrace : WordTrace (prefixWord ++ tailWord_4298713) baseStart_4298713 baseEnd_4298713 := by
    simpa [prefixWord, tailWord_4298713, baseEnd_4298713] using wordTrace_append hprefix tailTrace_4298713
  have hstable : (prefixWord ++ tailWord_4298713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298713).length < 2 ^ (prefixWord ++ tailWord_4298713).sum := by decide
  have hdescent : baseEnd_4298713 < baseStart_4298713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298749 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_4298749 : Nat := 118140960795 + 4298749 * 2 ^ 59
def prefixEnd_4298749 : Nat := 4983230072969 + 3 ^ 40 * 4298749 * 2
def baseEnd_4298749 : Nat := 2207324450034506858467919

theorem tailTrace_4298749 : CollatzResearch.WordTrace tailWord_4298749 prefixEnd_4298749 2207324450034506858467919 := by
  unfold tailWord_4298749
  simp only [CollatzResearch.WordTrace]
  refine ⟨156788256703374015724219301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104525504468916010482812867 156788256703374015724219301)
  ·
    refine ⟨29397798131882627948291119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156788256703374015724219301 29397798131882627948291119)
    ·
      refine ⟨44096697197823941922436679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29397798131882627948291119 44096697197823941922436679)
      ·
        refine ⟨66145045796735912883655019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44096697197823941922436679 66145045796735912883655019)
        ·
          refine ⟨99217568695103869325482529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66145045796735912883655019 99217568695103869325482529)
          ·
            refine ⟨74413176521327901994111897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99217568695103869325482529 74413176521327901994111897)
            ·
              refine ⟨55809882390995926495583923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74413176521327901994111897 55809882390995926495583923)
              ·
                refine ⟨83714823586493889743375885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55809882390995926495583923 83714823586493889743375885)
                ·
                  refine ⟨31393058844935208653765957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83714823586493889743375885 31393058844935208653765957)
                  ·
                    refine ⟨5886198533425351622581117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31393058844935208653765957 5886198533425351622581117)
                    ·
                      refine ⟨2207324450034506858467919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886198533425351622581117 2207324450034506858467919)
                      ·
                        rfl

theorem cell23_4298749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_4298749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298749 prefixEnd_4298749 := by exact prefixLift 4298749
  have htrace : WordTrace (prefixWord ++ tailWord_4298749) baseStart_4298749 baseEnd_4298749 := by
    simpa [prefixWord, tailWord_4298749, baseEnd_4298749] using wordTrace_append hprefix tailTrace_4298749
  have hstable : (prefixWord ++ tailWord_4298749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298749).length < 2 ^ (prefixWord ++ tailWord_4298749).sum := by decide
  have hdescent : baseEnd_4298749 < baseStart_4298749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298752 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 10]
def baseStart_4298752 : Nat := 118140960795 + 4298752 * 2 ^ 59
def prefixEnd_4298752 : Nat := 4983230072969 + 3 ^ 40 * 4298752 * 2
def baseEnd_4298752 : Nat := 245258443386274482970045

theorem tailTrace_4298752 : CollatzResearch.WordTrace tailWord_4298752 prefixEnd_4298752 245258443386274482970045 := by
  unfold tailWord_4298752
  simp only [CollatzResearch.WordTrace]
  refine ⟨78394183061181573618289255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104525577414908764824385673 78394183061181573618289255)
  ·
    refine ⟨117591274591772360427433883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78394183061181573618289255 117591274591772360427433883)
    ·
      refine ⟨176386911887658540641150825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117591274591772360427433883 176386911887658540641150825)
      ·
        refine ⟨132290183915743905480863119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176386911887658540641150825 132290183915743905480863119)
        ·
          refine ⟨198435275873615858221294679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132290183915743905480863119 198435275873615858221294679)
          ·
            refine ⟨297652913810423787331942019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198435275873615858221294679 297652913810423787331942019)
            ·
              refine ⟨446479370715635680997913029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297652913810423787331942019 446479370715635680997913029)
              ·
                refine ⟨83714882009181690187108693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446479370715635680997913029 83714882009181690187108693)
                ·
                  refine ⟨245258443386274482970045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83714882009181690187108693 245258443386274482970045)
                  ·
                    rfl

theorem cell23_4298752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_4298752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298752 prefixEnd_4298752 := by exact prefixLift 4298752
  have htrace : WordTrace (prefixWord ++ tailWord_4298752) baseStart_4298752 baseEnd_4298752 := by
    simpa [prefixWord, tailWord_4298752, baseEnd_4298752] using wordTrace_append hprefix tailTrace_4298752
  have hstable : (prefixWord ++ tailWord_4298752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298752).length < 2 ^ (prefixWord ++ tailWord_4298752).sum := by decide
  have hdescent : baseEnd_4298752 < baseStart_4298752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298786 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_4298786 : Nat := 118140960795 + 4298786 * 2 ^ 59
def prefixEnd_4298786 : Nat := 4983230072969 + 3 ^ 40 * 4298786 * 2
def baseEnd_4298786 : Nat := 245260383202080357078361

theorem tailTrace_4298786 : CollatzResearch.WordTrace tailWord_4298786 prefixEnd_4298786 245260383202080357078361 := by
  unfold tailWord_4298786
  simp only [CollatzResearch.WordTrace]
  refine ⟨39197401551059992760829053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104526404136159980695544141 39197401551059992760829053)
  ·
    refine ⟨14699025581647497285310895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39197401551059992760829053 14699025581647497285310895)
    ·
      refine ⟨22048538372471245927966343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14699025581647497285310895 22048538372471245927966343)
      ·
        refine ⟨33072807558706868891949515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22048538372471245927966343 33072807558706868891949515)
        ·
          refine ⟨49609211338060303337924273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33072807558706868891949515 49609211338060303337924273)
          ·
            refine ⟨37206908503545227503443205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49609211338060303337924273 37206908503545227503443205)
            ·
              refine ⟨6976295344414730156895601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37206908503545227503443205 6976295344414730156895601)
              ·
                refine ⟨5232221508311047617671701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6976295344414730156895601 5232221508311047617671701)
                ·
                  refine ⟨245260383202080357078361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5232221508311047617671701 245260383202080357078361)
                  ·
                    rfl

theorem cell23_4298786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_4298786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298786 prefixEnd_4298786 := by exact prefixLift 4298786
  have htrace : WordTrace (prefixWord ++ tailWord_4298786) baseStart_4298786 baseEnd_4298786 := by
    simpa [prefixWord, tailWord_4298786, baseEnd_4298786] using wordTrace_append hprefix tailTrace_4298786
  have hstable : (prefixWord ++ tailWord_4298786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298786).length < 2 ^ (prefixWord ++ tailWord_4298786).sum := by decide
  have hdescent : baseEnd_4298786 < baseStart_4298786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298813 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_4298813 : Nat := 118140960795 + 4298813 * 2 ^ 59
def prefixEnd_4298813 : Nat := 4983230072969 + 3 ^ 40 * 4298813 * 2
def baseEnd_4298813 : Nat := 2207357312796394608067625

theorem tailTrace_4298813 : CollatzResearch.WordTrace tailWord_4298813 prefixEnd_4298813 2207357312796394608067625 := by
  unfold tailWord_4298813
  simp only [CollatzResearch.WordTrace]
  refine ⟨156790590975142154654549093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104527060650094769769699395 156790590975142154654549093)
  ·
    refine ⟨29398235807839153997727955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156790590975142154654549093 29398235807839153997727955)
    ·
      refine ⟨44097353711758730996591933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29398235807839153997727955 44097353711758730996591933)
      ·
        refine ⟨16536507641909524123721975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44097353711758730996591933 16536507641909524123721975)
        ·
          refine ⟨24804761462864286185582963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16536507641909524123721975 24804761462864286185582963)
          ·
            refine ⟨37207142194296429278374445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24804761462864286185582963 37207142194296429278374445)
            ·
              refine ⟨13952678322861160979390417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37207142194296429278374445 13952678322861160979390417)
              ·
                refine ⟨10464508742145870734542813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13952678322861160979390417 10464508742145870734542813)
                ·
                  refine ⟨3924190778304701525453555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10464508742145870734542813 3924190778304701525453555)
                  ·
                    refine ⟨5886286167457052288180333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3924190778304701525453555 5886286167457052288180333)
                    ·
                      refine ⟨2207357312796394608067625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886286167457052288180333 2207357312796394608067625)
                      ·
                        rfl

theorem cell23_4298813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_4298813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298813 prefixEnd_4298813 := by exact prefixLift 4298813
  have htrace : WordTrace (prefixWord ++ tailWord_4298813) baseStart_4298813 baseEnd_4298813 := by
    simpa [prefixWord, tailWord_4298813, baseEnd_4298813] using wordTrace_append hprefix tailTrace_4298813
  have hstable : (prefixWord ++ tailWord_4298813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298813).length < 2 ^ (prefixWord ++ tailWord_4298813).sum := by decide
  have hdescent : baseEnd_4298813 < baseStart_4298813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298830 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_4298830 : Nat := 118140960795 + 4298830 * 2 ^ 59
def prefixEnd_4298830 : Nat := 4983230072969 + 3 ^ 40 * 4298830 * 2
def baseEnd_4298830 : Nat := 2207366041967521041555047

theorem tailTrace_4298830 : CollatzResearch.WordTrace tailWord_4298830 prefixEnd_4298830 2207366041967521041555047 := by
  unfold tailWord_4298830
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598901377010070819739743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104527474010720377705278629 19598901377010070819739743)
  ·
    refine ⟨29398352065515106229609615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19598901377010070819739743 29398352065515106229609615)
    ·
      refine ⟨44097528098272659344414423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29398352065515106229609615 44097528098272659344414423)
      ·
        refine ⟨66146292147408989016621635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44097528098272659344414423 66146292147408989016621635)
        ·
          refine ⟨99219438221113483524932453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66146292147408989016621635 99219438221113483524932453)
          ·
            refine ⟨18603644666458778160924835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99219438221113483524932453 18603644666458778160924835)
            ·
              refine ⟨27905466999688167241387253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18603644666458778160924835 27905466999688167241387253)
              ·
                refine ⟨2616137531220765678880055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27905466999688167241387253 2616137531220765678880055)
                ·
                  refine ⟨3924206296831148518320083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616137531220765678880055 3924206296831148518320083)
                  ·
                    refine ⟨5886309445246722777480125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3924206296831148518320083 5886309445246722777480125)
                    ·
                      refine ⟨2207366041967521041555047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886309445246722777480125 2207366041967521041555047)
                      ·
                        rfl

theorem cell23_4298830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_4298830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298830 prefixEnd_4298830 := by exact prefixLift 4298830
  have htrace : WordTrace (prefixWord ++ tailWord_4298830) baseStart_4298830 baseEnd_4298830 := by
    simpa [prefixWord, tailWord_4298830, baseEnd_4298830] using wordTrace_append hprefix tailTrace_4298830
  have hstable : (prefixWord ++ tailWord_4298830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298830).length < 2 ^ (prefixWord ++ tailWord_4298830).sum := by decide
  have hdescent : baseEnd_4298830 < baseStart_4298830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298849 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_4298849 : Nat := 118140960795 + 4298849 * 2 ^ 59
def prefixEnd_4298849 : Nat := 4983230072969 + 3 ^ 40 * 4298849 * 2
def baseEnd_4298849 : Nat := 2207375798099956467217459

theorem tailTrace_4298849 : CollatzResearch.WordTrace tailWord_4298849 prefixEnd_4298849 2207375798099956467217459 := by
  unfold tailWord_4298849
  simp only [CollatzResearch.WordTrace]
  refine ⟨156791904003011732802859601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104527936002007821868573067 156791904003011732802859601)
  ·
    refine ⟨117593928002258799602144701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156791904003011732802859601 117593928002258799602144701)
    ·
      refine ⟨44097723000847049850804263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117593928002258799602144701 44097723000847049850804263)
      ·
        refine ⟨66146584501270574776206395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44097723000847049850804263 66146584501270574776206395)
        ·
          refine ⟨99219876751905862164309593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66146584501270574776206395 99219876751905862164309593)
          ·
            refine ⟨74414907563929396623232195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99219876751905862164309593 74414907563929396623232195)
            ·
              refine ⟨111622361345894094934848293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74414907563929396623232195 111622361345894094934848293)
              ·
                refine ⟨20929192752355142800284055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111622361345894094934848293 20929192752355142800284055)
                ·
                  refine ⟨31393789128532714200426083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20929192752355142800284055 31393789128532714200426083)
                  ·
                    refine ⟨47090683692799071300639125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31393789128532714200426083 47090683692799071300639125)
                    ·
                      refine ⟨2207375798099956467217459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47090683692799071300639125 2207375798099956467217459)
                      ·
                        rfl

theorem cell23_4298849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_4298849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298849 prefixEnd_4298849 := by exact prefixLift 4298849
  have htrace : WordTrace (prefixWord ++ tailWord_4298849) baseStart_4298849 baseEnd_4298849 := by
    simpa [prefixWord, tailWord_4298849, baseEnd_4298849] using wordTrace_append hprefix tailTrace_4298849
  have hstable : (prefixWord ++ tailWord_4298849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298849).length < 2 ^ (prefixWord ++ tailWord_4298849).sum := by decide
  have hdescent : baseEnd_4298849 < baseStart_4298849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298866 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4298866 : Nat := 118140960795 + 4298866 * 2 ^ 59
def prefixEnd_4298866 : Nat := 4983230072969 + 3 ^ 40 * 4298866 * 2
def baseEnd_4298866 : Nat := 2207384527271082900704881

theorem tailTrace_4298866 : CollatzResearch.WordTrace tailWord_4298866 prefixEnd_4298866 2207384527271082900704881 := by
  unfold tailWord_4298866
  simp only [CollatzResearch.WordTrace]
  refine ⟨39198131010987536176557113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104528349362633429804152301 39198131010987536176557113)
  ·
    refine ⟨29398598258240652132417835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39198131010987536176557113 29398598258240652132417835)
    ·
      refine ⟨44097897387360978198626753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29398598258240652132417835 44097897387360978198626753)
      ·
        refine ⟨33073423040520733648970065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44097897387360978198626753 33073423040520733648970065)
        ·
          refine ⟨24805067280390550236727549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33073423040520733648970065 24805067280390550236727549)
          ·
            refine ⟨9301900230146456338772831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24805067280390550236727549 9301900230146456338772831)
            ·
              refine ⟨13952850345219684508159247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301900230146456338772831 13952850345219684508159247)
              ·
                refine ⟨20929275517829526762238871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13952850345219684508159247 20929275517829526762238871)
                ·
                  refine ⟨31393913276744290143358307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20929275517829526762238871 31393913276744290143358307)
                  ·
                    refine ⟨47090869915116435215037461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31393913276744290143358307 47090869915116435215037461)
                    ·
                      refine ⟨2207384527271082900704881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47090869915116435215037461 2207384527271082900704881)
                      ·
                        rfl

theorem cell23_4298866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4298866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298866 prefixEnd_4298866 := by exact prefixLift 4298866
  have htrace : WordTrace (prefixWord ++ tailWord_4298866) baseStart_4298866 baseEnd_4298866 := by
    simpa [prefixWord, tailWord_4298866, baseEnd_4298866] using wordTrace_append hprefix tailTrace_4298866
  have hstable : (prefixWord ++ tailWord_4298866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298866).length < 2 ^ (prefixWord ++ tailWord_4298866).sum := by decide
  have hdescent : baseEnd_4298866 < baseStart_4298866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298870 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4298870 : Nat := 118140960795 + 4298870 * 2 ^ 59
def prefixEnd_4298870 : Nat := 4983230072969 + 3 ^ 40 * 4298870 * 2
def baseEnd_4298870 : Nat := 2207386581193700885054863

theorem tailTrace_4298870 : CollatzResearch.WordTrace tailWord_4298870 prefixEnd_4298870 2207386581193700885054863 := by
  unfold tailWord_4298870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9799541870995978336835879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104528446623957102259582709 9799541870995978336835879)
  ·
    refine ⟨14699312806493967505253819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9799541870995978336835879 14699312806493967505253819)
    ·
      refine ⟨22048969209740951257880729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14699312806493967505253819 22048969209740951257880729)
      ·
        refine ⟨16536726907305713443410547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22048969209740951257880729 16536726907305713443410547)
        ·
          refine ⟨24805090360958570165115821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16536726907305713443410547 24805090360958570165115821)
          ·
            refine ⟨9301908885359463811918433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24805090360958570165115821 9301908885359463811918433)
            ·
              refine ⟨6976431664019597858938825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9301908885359463811918433 6976431664019597858938825)
              ·
                refine ⟨5232323748014698394204119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6976431664019597858938825 5232323748014698394204119)
                ·
                  refine ⟨7848485622022047591306179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5232323748014698394204119 7848485622022047591306179)
                  ·
                    refine ⟨11772728433033071386959269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7848485622022047591306179 11772728433033071386959269)
                    ·
                      refine ⟨2207386581193700885054863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11772728433033071386959269 2207386581193700885054863)
                      ·
                        rfl

theorem cell23_4298870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4298870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298870 prefixEnd_4298870 := by exact prefixLift 4298870
  have htrace : WordTrace (prefixWord ++ tailWord_4298870) baseStart_4298870 baseEnd_4298870 := by
    simpa [prefixWord, tailWord_4298870, baseEnd_4298870] using wordTrace_append hprefix tailTrace_4298870
  have hstable : (prefixWord ++ tailWord_4298870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298870).length < 2 ^ (prefixWord ++ tailWord_4298870).sum := by decide
  have hdescent : baseEnd_4298870 < baseStart_4298870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298873 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 3]
def baseStart_4298873 : Nat := 118140960795 + 4298873 * 2 ^ 59
def prefixEnd_4298873 : Nat := 4983230072969 + 3 ^ 40 * 4298873 * 2
def baseEnd_4298873 : Nat := 2207388121635664373317349

theorem tailTrace_4298873 : CollatzResearch.WordTrace tailWord_4298873 prefixEnd_4298873 2207388121635664373317349 := by
  unfold tailWord_4298873
  simp only [CollatzResearch.WordTrace]
  refine ⟨156792779354924784901733273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104528519569949856601155515 156792779354924784901733273)
  ·
    refine ⟨117594584516193588676299955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156792779354924784901733273 117594584516193588676299955)
    ·
      refine ⟨176391876774290383014449933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117594584516193588676299955 176391876774290383014449933)
      ·
        refine ⟨66146953790358893630418725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176391876774290383014449933 66146953790358893630418725)
        ·
          refine ⟨12402553835692292555703511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66146953790358893630418725 12402553835692292555703511)
          ·
            refine ⟨18603830753538438833555267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12402553835692292555703511 18603830753538438833555267)
            ·
              refine ⟨27905746130307658250332901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18603830753538438833555267 27905746130307658250332901)
              ·
                refine ⟨5232327399432685921937419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27905746130307658250332901 5232327399432685921937419)
                ·
                  refine ⟨7848491099149028882906129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5232327399432685921937419 7848491099149028882906129)
                  ·
                    refine ⟨5886368324361771662179597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7848491099149028882906129 5886368324361771662179597)
                    ·
                      refine ⟨2207388121635664373317349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886368324361771662179597 2207388121635664373317349)
                      ·
                        rfl

theorem cell23_4298873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_4298873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298873 prefixEnd_4298873 := by exact prefixLift 4298873
  have htrace : WordTrace (prefixWord ++ tailWord_4298873) baseStart_4298873 baseEnd_4298873 := by
    simpa [prefixWord, tailWord_4298873, baseEnd_4298873] using wordTrace_append hprefix tailTrace_4298873
  have hstable : (prefixWord ++ tailWord_4298873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298873).length < 2 ^ (prefixWord ++ tailWord_4298873).sum := by decide
  have hdescent : baseEnd_4298873 < baseStart_4298873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298876 : List Nat := [2, 2, 2, 1, 1, 4, 4, 7]
def baseStart_4298876 : Nat := 118140960795 + 4298876 * 2 ^ 59
def prefixEnd_4298876 : Nat := 4983230072969 + 3 ^ 40 * 4298876 * 2
def baseEnd_4298876 : Nat := 81755172669541772651105

theorem tailTrace_4298876 : CollatzResearch.WordTrace tailWord_4298876 prefixEnd_4298876 81755172669541772651105 := by
  unfold tailWord_4298876
  simp only [CollatzResearch.WordTrace]
  refine ⟨78396444386956958207046241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104528592515942610942728321 78396444386956958207046241)
  ·
    refine ⟨58797333290217718655284681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78396444386956958207046241 58797333290217718655284681)
    ·
      refine ⟨44097999967663288991463511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58797333290217718655284681 44097999967663288991463511)
      ·
        refine ⟨66146999951494933487195267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44097999967663288991463511 66146999951494933487195267)
        ·
          refine ⟨99220499927242400230792901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66146999951494933487195267 99220499927242400230792901)
          ·
            refine ⟨18603843736357950043273669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99220499927242400230792901 18603843736357950043273669)
            ·
              refine ⟨3488220700567115633113813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18603843736357950043273669 3488220700567115633113813)
              ·
                refine ⟨81755172669541772651105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3488220700567115633113813 81755172669541772651105)
                ·
                  rfl

theorem cell23_4298876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 7].length) (baseStart_4298876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298876 prefixEnd_4298876 := by exact prefixLift 4298876
  have htrace : WordTrace (prefixWord ++ tailWord_4298876) baseStart_4298876 baseEnd_4298876 := by
    simpa [prefixWord, tailWord_4298876, baseEnd_4298876] using wordTrace_append hprefix tailTrace_4298876
  have hstable : (prefixWord ++ tailWord_4298876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298876).length < 2 ^ (prefixWord ++ tailWord_4298876).sum := by decide
  have hdescent : baseEnd_4298876 < baseStart_4298876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298887 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_4298887 : Nat := 118140960795 + 4298887 * 2 ^ 59
def prefixEnd_4298887 : Nat := 4983230072969 + 3 ^ 40 * 4298887 * 2
def baseEnd_4298887 : Nat := 2207395310364827318542285

theorem tailTrace_4298887 : CollatzResearch.WordTrace tailWord_4298887 prefixEnd_4298887 2207395310364827318542285 := by
  unfold tailWord_4298887
  simp only [CollatzResearch.WordTrace]
  refine ⟨156793289976874065292742915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104528859984582710195161943 156793289976874065292742915)
  ·
    refine ⟨235189934965311097939114373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156793289976874065292742915 235189934965311097939114373)
    ·
      refine ⟨44098112805995830863583945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235189934965311097939114373 44098112805995830863583945)
      ·
        refine ⟨33073584604496873147687959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44098112805995830863583945 33073584604496873147687959)
        ·
          refine ⟨49610376906745309721531939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33073584604496873147687959 49610376906745309721531939)
          ·
            refine ⟨74415565360117964582297909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49610376906745309721531939 74415565360117964582297909)
            ·
              refine ⟨6976459252511059179590429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74415565360117964582297909 6976459252511059179590429)
              ·
                refine ⟨2616172219691647192346411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6976459252511059179590429 2616172219691647192346411)
                ·
                  refine ⟨3924258329537470788519617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616172219691647192346411 3924258329537470788519617)
                  ·
                    refine ⟨2943193747153103091389713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3924258329537470788519617 2943193747153103091389713)
                    ·
                      refine ⟨2207395310364827318542285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943193747153103091389713 2207395310364827318542285)
                      ·
                        rfl

theorem cell23_4298887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_4298887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298887 prefixEnd_4298887 := by exact prefixLift 4298887
  have htrace : WordTrace (prefixWord ++ tailWord_4298887) baseStart_4298887 baseEnd_4298887 := by
    simpa [prefixWord, tailWord_4298887, baseEnd_4298887] using wordTrace_append hprefix tailTrace_4298887
  have hstable : (prefixWord ++ tailWord_4298887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298887).length < 2 ^ (prefixWord ++ tailWord_4298887).sum := by decide
  have hdescent : baseEnd_4298887 < baseStart_4298887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298899 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_4298899 : Nat := 118140960795 + 4298899 * 2 ^ 59
def prefixEnd_4298899 : Nat := 4983230072969 + 3 ^ 40 * 4298899 * 2
def baseEnd_4298899 : Nat := 2207401472132681271592229

theorem tailTrace_4298899 : CollatzResearch.WordTrace tailWord_4298899 prefixEnd_4298899 2207401472132681271592229 := by
  unfold tailWord_4298899
  simp only [CollatzResearch.WordTrace]
  refine ⟨156793727652830591342179751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104529151768553727561453167 156793727652830591342179751)
  ·
    refine ⟨235190591479245887013269627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156793727652830591342179751 235190591479245887013269627)
    ·
      refine ⟨352785887218868830519904441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235190591479245887013269627 352785887218868830519904441)
      ·
        refine ⟨264589415414151622889928331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352785887218868830519904441 264589415414151622889928331)
        ·
          refine ⟨396884123121227434334892497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264589415414151622889928331 396884123121227434334892497)
          ·
            refine ⟨297663092340920575751169373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396884123121227434334892497 297663092340920575751169373)
            ·
              refine ⟨111623659627845215906688515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297663092340920575751169373 111623659627845215906688515)
              ·
                refine ⟨167435489441767823860032773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111623659627845215906688515 167435489441767823860032773)
                ·
                  refine ⟨31394154270331466973756145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167435489441767823860032773 31394154270331466973756145)
                  ·
                    refine ⟨23545615702748600230317109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31394154270331466973756145 23545615702748600230317109)
                    ·
                      refine ⟨2207401472132681271592229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23545615702748600230317109 2207401472132681271592229)
                      ·
                        rfl

theorem cell23_4298899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_4298899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298899 prefixEnd_4298899 := by exact prefixLift 4298899
  have htrace : WordTrace (prefixWord ++ tailWord_4298899) baseStart_4298899 baseEnd_4298899 := by
    simpa [prefixWord, tailWord_4298899, baseEnd_4298899] using wordTrace_append hprefix tailTrace_4298899
  have hstable : (prefixWord ++ tailWord_4298899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298899).length < 2 ^ (prefixWord ++ tailWord_4298899).sum := by decide
  have hdescent : baseEnd_4298899 < baseStart_4298899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298904 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4298904 : Nat := 118140960795 + 4298904 * 2 ^ 59
def prefixEnd_4298904 : Nat := 4983230072969 + 3 ^ 40 * 4298904 * 2
def baseEnd_4298904 : Nat := 2207404039535953752029707

theorem tailTrace_4298904 : CollatzResearch.WordTrace tailWord_4298904 prefixEnd_4298904 2207404039535953752029707 := by
  unfold tailWord_4298904
  simp only [CollatzResearch.WordTrace]
  refine ⟨78396955008906238598055883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104529273345208318130741177 78396955008906238598055883)
  ·
    refine ⟨117595432513359357897083825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78396955008906238598055883 117595432513359357897083825)
    ·
      refine ⟨88196574385019518422812869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117595432513359357897083825 88196574385019518422812869)
      ·
        refine ⟨16536857697191159704277413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88196574385019518422812869 16536857697191159704277413)
        ·
          refine ⟨3100660818223342444552015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16536857697191159704277413 3100660818223342444552015)
          ·
            refine ⟨4650991227335013666828023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100660818223342444552015 4650991227335013666828023)
            ·
              refine ⟨6976486841002520500242035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650991227335013666828023 6976486841002520500242035)
              ·
                refine ⟨10464730261503780750363053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6976486841002520500242035 10464730261503780750363053)
                ·
                  refine ⟨3924273848063917781386145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10464730261503780750363053 3924273848063917781386145)
                  ·
                    refine ⟨2943205386047938336039609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3924273848063917781386145 2943205386047938336039609)
                    ·
                      refine ⟨2207404039535953752029707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943205386047938336039609 2207404039535953752029707)
                      ·
                        rfl

theorem cell23_4298904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4298904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298904 prefixEnd_4298904 := by exact prefixLift 4298904
  have htrace : WordTrace (prefixWord ++ tailWord_4298904) baseStart_4298904 baseEnd_4298904 := by
    simpa [prefixWord, tailWord_4298904, baseEnd_4298904] using wordTrace_append hprefix tailTrace_4298904
  have hstable : (prefixWord ++ tailWord_4298904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298904).length < 2 ^ (prefixWord ++ tailWord_4298904).sum := by decide
  have hdescent : baseEnd_4298904 < baseStart_4298904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298973 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4298973 : Nat := 118140960795 + 4298973 * 2 ^ 59
def prefixEnd_4298973 : Nat := 4983230072969 + 3 ^ 40 * 4298973 * 2
def baseEnd_4298973 : Nat := 2207439469701113982066889

theorem tailTrace_4298973 : CollatzResearch.WordTrace tailWord_4298973 prefixEnd_4298973 2207439469701113982066889 := by
  unfold tailWord_4298973
  simp only [CollatzResearch.WordTrace]
  refine ⟨156796426654562501980373573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104530951103041667986915715 156796426654562501980373573)
  ·
    refine ⟨29399329997730469121320045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156796426654562501980373573 29399329997730469121320045)
    ·
      refine ⟨11024748749148925920495017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29399329997730469121320045 11024748749148925920495017)
      ·
        refine ⟨8268561561861694440371263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11024748749148925920495017 8268561561861694440371263)
        ·
          refine ⟨12402842342792541660556895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268561561861694440371263 12402842342792541660556895)
          ·
            refine ⟨18604263514188812490835343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12402842342792541660556895 18604263514188812490835343)
            ·
              refine ⟨27906395271283218736253015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18604263514188812490835343 27906395271283218736253015)
              ·
                refine ⟨41859592906924828104379523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27906395271283218736253015 41859592906924828104379523)
                ·
                  refine ⟨62789389360387242156569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41859592906924828104379523 62789389360387242156569285)
                  ·
                    refine ⟨11773010505072607904356741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62789389360387242156569285 11773010505072607904356741)
                    ·
                      refine ⟨2207439469701113982066889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11773010505072607904356741 2207439469701113982066889)
                      ·
                        rfl

theorem cell23_4298973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4298973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298973 prefixEnd_4298973 := by exact prefixLift 4298973
  have htrace : WordTrace (prefixWord ++ tailWord_4298973) baseStart_4298973 baseEnd_4298973 := by
    simpa [prefixWord, tailWord_4298973, baseEnd_4298973] using wordTrace_append hprefix tailTrace_4298973
  have hstable : (prefixWord ++ tailWord_4298973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298973).length < 2 ^ (prefixWord ++ tailWord_4298973).sum := by decide
  have hdescent : baseEnd_4298973 < baseStart_4298973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4298983 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 7]
def baseStart_4298983 : Nat := 118140960795 + 4298983 * 2 ^ 59
def prefixEnd_4298983 : Nat := 4983230072969 + 3 ^ 40 * 4298983 * 2
def baseEnd_4298983 : Nat := 245271622723073215882427

theorem tailTrace_4298983 : CollatzResearch.WordTrace tailWord_4298983 prefixEnd_4298983 245271622723073215882427 := by
  unfold tailWord_4298983
  simp only [CollatzResearch.WordTrace]
  refine ⟨156796791384526273688237603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104531194256350849125491735 156796791384526273688237603)
  ·
    refine ⟨235195187076789410532356405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156796791384526273688237603 235195187076789410532356405)
    ·
      refine ⟨22049548788449007237408413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235195187076789410532356405 22049548788449007237408413)
      ·
        refine ⟨8268580795668377714028155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22049548788449007237408413 8268580795668377714028155)
        ·
          refine ⟨12402871193502566571042233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268580795668377714028155 12402871193502566571042233)
          ·
            refine ⟨9302153395126924928281675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12402871193502566571042233 9302153395126924928281675)
            ·
              refine ⟨13953230092690387392422513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9302153395126924928281675 13953230092690387392422513)
              ·
                refine ⟨10464922569517790544316885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13953230092690387392422513 10464922569517790544316885)
                ·
                  refine ⟨245271622723073215882427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10464922569517790544316885 245271622723073215882427)
                  ·
                    rfl

theorem cell23_4298983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 7].length) (baseStart_4298983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4298983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4298983 prefixEnd_4298983 := by exact prefixLift 4298983
  have htrace : WordTrace (prefixWord ++ tailWord_4298983) baseStart_4298983 baseEnd_4298983 := by
    simpa [prefixWord, tailWord_4298983, baseEnd_4298983] using wordTrace_append hprefix tailTrace_4298983
  have hstable : (prefixWord ++ tailWord_4298983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4298983).length < 2 ^ (prefixWord ++ tailWord_4298983).sum := by decide
  have hdescent : baseEnd_4298983 < baseStart_4298983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4298983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299010 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4299010 : Nat := 118140960795 + 4299010 * 2 ^ 59
def prefixEnd_4299010 : Nat := 4983230072969 + 3 ^ 40 * 4299010 * 2
def baseEnd_4299010 : Nat := 2207458468485330337304219

theorem tailTrace_4299010 : CollatzResearch.WordTrace tailWord_4299010 prefixEnd_4299010 2207458468485330337304219 := by
  unfold tailWord_4299010
  simp only [CollatzResearch.WordTrace]
  refine ⟨39199444038857114324867621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104531850770285638199646989 39199444038857114324867621)
  ·
    refine ⟨7349895757285708935912679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39199444038857114324867621 7349895757285708935912679)
    ·
      refine ⟨11024843635928563403869019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7349895757285708935912679 11024843635928563403869019)
      ·
        refine ⟨16537265453892845105803529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11024843635928563403869019 16537265453892845105803529)
        ·
          refine ⟨12402949090419633829352647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16537265453892845105803529 12402949090419633829352647)
          ·
            refine ⟨18604423635629450744028971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12402949090419633829352647 18604423635629450744028971)
            ·
              refine ⟨27906635453444176116043457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18604423635629450744028971 27906635453444176116043457)
              ·
                refine ⟨20929976590083132087032593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27906635453444176116043457 20929976590083132087032593)
                ·
                  refine ⟨15697482442562349065274445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20929976590083132087032593 15697482442562349065274445)
                  ·
                    refine ⟨5886555915960880899477917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15697482442562349065274445 5886555915960880899477917)
                    ·
                      refine ⟨2207458468485330337304219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886555915960880899477917 2207458468485330337304219)
                      ·
                        rfl

theorem cell23_4299010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4299010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299010 prefixEnd_4299010 := by exact prefixLift 4299010
  have htrace : WordTrace (prefixWord ++ tailWord_4299010) baseStart_4299010 baseEnd_4299010 := by
    simpa [prefixWord, tailWord_4299010, baseEnd_4299010] using wordTrace_append hprefix tailTrace_4299010
  have hstable : (prefixWord ++ tailWord_4299010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299010).length < 2 ^ (prefixWord ++ tailWord_4299010).sum := by decide
  have hdescent : baseEnd_4299010 < baseStart_4299010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299043 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 3, 4]
def baseStart_4299043 : Nat := 118140960795 + 4299043 * 2 ^ 59
def prefixEnd_4299043 : Nat := 4983230072969 + 3 ^ 40 * 4299043 * 2
def baseEnd_4299043 : Nat := 735825137782309569397189

theorem tailTrace_4299043 : CollatzResearch.WordTrace tailWord_4299043 prefixEnd_4299043 735825137782309569397189 := by
  unfold tailWord_4299043
  simp only [CollatzResearch.WordTrace]
  refine ⟨156798979764308903935421783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104532653176205935956947855 156798979764308903935421783)
  ·
    refine ⟨235198469646463355903132675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156798979764308903935421783 235198469646463355903132675)
    ·
      refine ⟨352797704469695033854699013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235198469646463355903132675 352797704469695033854699013)
      ·
        refine ⟨66149569588067818847756065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 352797704469695033854699013 66149569588067818847756065)
        ·
          refine ⟨49612177191050864135817049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66149569588067818847756065 49612177191050864135817049)
          ·
            refine ⟨37209132893288148101862787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49612177191050864135817049 37209132893288148101862787)
            ·
              refine ⟨55813699339932222152794181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37209132893288148101862787 55813699339932222152794181)
              ·
                refine ⟨10465068626237291653648909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55813699339932222152794181 10465068626237291653648909)
                ·
                  refine ⟨3924400734838984370118341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10465068626237291653648909 3924400734838984370118341)
                  ·
                    refine ⟨735825137782309569397189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3924400734838984370118341 735825137782309569397189)
                    ·
                      rfl

theorem cell23_4299043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 4].length) (baseStart_4299043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299043 prefixEnd_4299043 := by exact prefixLift 4299043
  have htrace : WordTrace (prefixWord ++ tailWord_4299043) baseStart_4299043 baseEnd_4299043 := by
    simpa [prefixWord, tailWord_4299043, baseEnd_4299043] using wordTrace_append hprefix tailTrace_4299043
  have hstable : (prefixWord ++ tailWord_4299043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299043).length < 2 ^ (prefixWord ++ tailWord_4299043).sum := by decide
  have hdescent : baseEnd_4299043 < baseStart_4299043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299070 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_4299070 : Nat := 118140960795 + 4299070 * 2 ^ 59
def prefixEnd_4299070 : Nat := 4983230072969 + 3 ^ 40 * 4299070 * 2
def baseEnd_4299070 : Nat := 2207489277324600102553943

theorem tailTrace_4299070 : CollatzResearch.WordTrace tailWord_4299070 prefixEnd_4299070 2207489277324600102553943 := by
  unfold tailWord_4299070
  simp only [CollatzResearch.WordTrace]
  refine ⟨19599995566901385943331833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104533309690140725031103109 19599995566901385943331833)
  ·
    refine ⟨14699996675176039457498875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19599995566901385943331833 14699996675176039457498875)
    ·
      refine ⟨22049995012764059186248313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14699996675176039457498875 22049995012764059186248313)
      ·
        refine ⟨16537496259573044389686235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22049995012764059186248313 16537496259573044389686235)
        ·
          refine ⟨24806244389359566584529353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16537496259573044389686235 24806244389359566584529353)
          ·
            refine ⟨18604683292019674938397015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24806244389359566584529353 18604683292019674938397015)
            ·
              refine ⟨27907024938029512407595523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18604683292019674938397015 27907024938029512407595523)
              ·
                refine ⟨41860537407044268611393285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27907024938029512407595523 41860537407044268611393285)
                ·
                  refine ⟨7848850763820800364636241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41860537407044268611393285 7848850763820800364636241)
                  ·
                    refine ⟨5886638072865600273477181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7848850763820800364636241 5886638072865600273477181)
                    ·
                      refine ⟨2207489277324600102553943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886638072865600273477181 2207489277324600102553943)
                      ·
                        rfl

theorem cell23_4299070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_4299070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299070 prefixEnd_4299070 := by exact prefixLift 4299070
  have htrace : WordTrace (prefixWord ++ tailWord_4299070) baseStart_4299070 baseEnd_4299070 := by
    simpa [prefixWord, tailWord_4299070, baseEnd_4299070] using wordTrace_append hprefix tailTrace_4299070
  have hstable : (prefixWord ++ tailWord_4299070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299070).length < 2 ^ (prefixWord ++ tailWord_4299070).sum := by decide
  have hdescent : baseEnd_4299070 < baseStart_4299070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299090 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_4299090 : Nat := 118140960795 + 4299090 * 2 ^ 59
def prefixEnd_4299090 : Nat := 4983230072969 + 3 ^ 40 * 4299090 * 2
def baseEnd_4299090 : Nat := 245277727437521113811539

theorem tailTrace_4299090 : CollatzResearch.WordTrace tailWord_4299090 prefixEnd_4299090 245277727437521113811539 := by
  unfold tailWord_4299090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39200173498784657740595681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104533795996759087308255149 39200173498784657740595681)
  ·
    refine ⟨29400130124088493305446761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39200173498784657740595681 29400130124088493305446761)
    ·
      refine ⟨22050097593066369979085071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29400130124088493305446761 22050097593066369979085071)
      ·
        refine ⟨33075146389599554968627607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22050097593066369979085071 33075146389599554968627607)
        ·
          refine ⟨49612719584399332452941411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33075146389599554968627607 49612719584399332452941411)
          ·
            refine ⟨74419079376598998679412117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49612719584399332452941411 74419079376598998679412117)
            ·
              refine ⟨3488394345778078063097443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74419079376598998679412117 3488394345778078063097443)
              ·
                refine ⟨5232591518667117094646165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488394345778078063097443 5232591518667117094646165)
                ·
                  refine ⟨245277727437521113811539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5232591518667117094646165 245277727437521113811539)
                  ·
                    rfl

theorem cell23_4299090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_4299090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299090 prefixEnd_4299090 := by exact prefixLift 4299090
  have htrace : WordTrace (prefixWord ++ tailWord_4299090) baseStart_4299090 baseEnd_4299090 := by
    simpa [prefixWord, tailWord_4299090, baseEnd_4299090] using wordTrace_append hprefix tailTrace_4299090
  have hstable : (prefixWord ++ tailWord_4299090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299090).length < 2 ^ (prefixWord ++ tailWord_4299090).sum := by decide
  have hdescent : baseEnd_4299090 < baseStart_4299090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299096 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4299096 : Nat := 118140960795 + 4299096 * 2 ^ 59
def prefixEnd_4299096 : Nat := 4983230072969 + 3 ^ 40 * 4299096 * 2
def baseEnd_4299096 : Nat := 2207502627821617000828823

theorem tailTrace_4299096 : CollatzResearch.WordTrace tailWord_4299096 prefixEnd_4299096 2207502627821617000828823 := by
  unfold tailWord_4299096
  simp only [CollatzResearch.WordTrace]
  refine ⟨78400456416558446993550571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104533941888744595991400761 78400456416558446993550571)
  ·
    refine ⟨117600684624837670490325857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78400456416558446993550571 117600684624837670490325857)
    ·
      refine ⟨88200513468628252867744393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117600684624837670490325857 88200513468628252867744393)
      ·
        refine ⟨66150385101471189650808295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88200513468628252867744393 66150385101471189650808295)
        ·
          refine ⟨99225577652206784476212443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66150385101471189650808295 99225577652206784476212443)
          ·
            refine ⟨148838366478310176714318665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99225577652206784476212443 148838366478310176714318665)
            ·
              refine ⟨111628774858732632535738999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148838366478310176714318665 111628774858732632535738999)
              ·
                refine ⟨167443162288098948803608499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111628774858732632535738999 167443162288098948803608499)
                ·
                  refine ⟨251164743432148423205412749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167443162288098948803608499 251164743432148423205412749)
                  ·
                    refine ⟨94186778787055658702029781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251164743432148423205412749 94186778787055658702029781)
                    ·
                      refine ⟨2207502627821617000828823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94186778787055658702029781 2207502627821617000828823)
                      ·
                        rfl

theorem cell23_4299096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4299096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299096 prefixEnd_4299096 := by exact prefixLift 4299096
  have htrace : WordTrace (prefixWord ++ tailWord_4299096) baseStart_4299096 baseEnd_4299096 := by
    simpa [prefixWord, tailWord_4299096, baseEnd_4299096] using wordTrace_append hprefix tailTrace_4299096
  have hstable : (prefixWord ++ tailWord_4299096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299096).length < 2 ^ (prefixWord ++ tailWord_4299096).sum := by decide
  have hdescent : baseEnd_4299096 < baseStart_4299096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299143 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_4299143 : Nat := 118140960795 + 4299143 * 2 ^ 59
def prefixEnd_4299143 : Nat := 4983230072969 + 3 ^ 40 * 4299143 * 2
def baseEnd_4299143 : Nat := 2207526761412378316941107

theorem tailTrace_4299143 : CollatzResearch.WordTrace tailWord_4299143 prefixEnd_4299143 2207526761412378316941107 := by
  unfold tailWord_4299143
  simp only [CollatzResearch.WordTrace]
  refine ⟨156802627063946621014062083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104535084709297747342708055 156802627063946621014062083)
  ·
    refine ⟨235203940595919931521093125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156802627063946621014062083 235203940595919931521093125)
    ·
      refine ⟨44100738861734987160204961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235203940595919931521093125 44100738861734987160204961)
      ·
        refine ⟨33075554146301240370153721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44100738861734987160204961 33075554146301240370153721)
        ·
          refine ⟨24806665609725930277615291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33075554146301240370153721 24806665609725930277615291)
          ·
            refine ⟨37209998414588895416422937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24806665609725930277615291 37209998414588895416422937)
            ·
              refine ⟨27907498810941671562317203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37209998414588895416422937 27907498810941671562317203)
              ·
                refine ⟨41861248216412507343475805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27907498810941671562317203 41861248216412507343475805)
                ·
                  refine ⟨15697968081154690253803427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41861248216412507343475805 15697968081154690253803427)
                  ·
                    refine ⟨23546952121732035380705141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15697968081154690253803427 23546952121732035380705141)
                    ·
                      refine ⟨2207526761412378316941107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23546952121732035380705141 2207526761412378316941107)
                      ·
                        rfl

theorem cell23_4299143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_4299143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299143 prefixEnd_4299143 := by exact prefixLift 4299143
  have htrace : WordTrace (prefixWord ++ tailWord_4299143) baseStart_4299143 baseEnd_4299143 := by
    simpa [prefixWord, tailWord_4299143, baseEnd_4299143] using wordTrace_append hprefix tailTrace_4299143
  have hstable : (prefixWord ++ tailWord_4299143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299143).length < 2 ^ (prefixWord ++ tailWord_4299143).sum := by decide
  have hdescent : baseEnd_4299143 < baseStart_4299143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299150 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_4299150 : Nat := 118140960795 + 4299150 * 2 ^ 59
def prefixEnd_4299150 : Nat := 4983230072969 + 3 ^ 40 * 4299150 * 2
def baseEnd_4299150 : Nat := 735843451925653263184525

theorem tailTrace_4299150 : CollatzResearch.WordTrace tailWord_4299150 prefixEnd_4299150 735843451925653263184525 := by
  unfold tailWord_4299150
  simp only [CollatzResearch.WordTrace]
  refine ⟨19600360296865157651195863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104535254916614174139711269 19600360296865157651195863)
  ·
    refine ⟨29400540445297736476793795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19600360296865157651195863 29400540445297736476793795)
    ·
      refine ⟨44100810667946604715190693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29400540445297736476793795 44100810667946604715190693)
      ·
        refine ⟨8268902000239988384098255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44100810667946604715190693 8268902000239988384098255)
        ·
          refine ⟨12403353000359982576147383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268902000239988384098255 12403353000359982576147383)
          ·
            refine ⟨18605029500539973864221075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12403353000359982576147383 18605029500539973864221075)
            ·
              refine ⟨27907544250809960796331613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18605029500539973864221075 27907544250809960796331613)
              ·
                refine ⟨10465329094053735298624355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27907544250809960796331613 10465329094053735298624355)
                ·
                  refine ⟨15697993641080602947936533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10465329094053735298624355 15697993641080602947936533)
                  ·
                    refine ⟨735843451925653263184525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15697993641080602947936533 735843451925653263184525)
                    ·
                      rfl

theorem cell23_4299150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_4299150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299150 prefixEnd_4299150 := by exact prefixLift 4299150
  have htrace : WordTrace (prefixWord ++ tailWord_4299150) baseStart_4299150 baseEnd_4299150 := by
    simpa [prefixWord, tailWord_4299150, baseEnd_4299150] using wordTrace_append hprefix tailTrace_4299150
  have hstable : (prefixWord ++ tailWord_4299150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299150).length < 2 ^ (prefixWord ++ tailWord_4299150).sum := by decide
  have hdescent : baseEnd_4299150 < baseStart_4299150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299170 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4299170 : Nat := 118140960795 + 4299170 * 2 ^ 59
def prefixEnd_4299170 : Nat := 4983230072969 + 3 ^ 40 * 4299170 * 2
def baseEnd_4299170 : Nat := 2207540625390049711303483

theorem tailTrace_4299170 : CollatzResearch.WordTrace tailWord_4299170 prefixEnd_4299170 2207540625390049711303483 := by
  unfold tailWord_4299170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39200902958712201156323741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104535741223232536416863309 39200902958712201156323741)
  ·
    refine ⟨14700338609517075433621403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39200902958712201156323741 14700338609517075433621403)
    ·
      refine ⟨22050507914275613150432105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14700338609517075433621403 22050507914275613150432105)
      ·
        refine ⟨16537880935706709862824079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22050507914275613150432105 16537880935706709862824079)
        ·
          refine ⟨24806821403560064794236119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16537880935706709862824079 24806821403560064794236119)
          ·
            refine ⟨37210232105340097191354179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24806821403560064794236119 37210232105340097191354179)
            ·
              refine ⟨55815348158010145787031269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37210232105340097191354179 55815348158010145787031269)
              ·
                refine ⟨10465377779626902335068363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55815348158010145787031269 10465377779626902335068363)
                ·
                  refine ⟨15698066669440353502602545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10465377779626902335068363 15698066669440353502602545)
                  ·
                    refine ⟨11773550002080265126951909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15698066669440353502602545 11773550002080265126951909)
                    ·
                      refine ⟨2207540625390049711303483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11773550002080265126951909 2207540625390049711303483)
                      ·
                        rfl

theorem cell23_4299170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4299170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299170 prefixEnd_4299170 := by exact prefixLift 4299170
  have htrace : WordTrace (prefixWord ++ tailWord_4299170) baseStart_4299170 baseEnd_4299170 := by
    simpa [prefixWord, tailWord_4299170, baseEnd_4299170] using wordTrace_append hprefix tailTrace_4299170
  have hstable : (prefixWord ++ tailWord_4299170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299170).length < 2 ^ (prefixWord ++ tailWord_4299170).sum := by decide
  have hdescent : baseEnd_4299170 < baseStart_4299170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299201 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4299201 : Nat := 118140960795 + 4299201 * 2 ^ 59
def prefixEnd_4299201 : Nat := 4983230072969 + 3 ^ 40 * 4299201 * 2
def baseEnd_4299201 : Nat := 735852181096779696671947

theorem tailTrace_4299201 : CollatzResearch.WordTrace tailWord_4299201 prefixEnd_4299201 735852181096779696671947 := by
  unfold tailWord_4299201
  simp only [CollatzResearch.WordTrace]
  refine ⟨156804742497736496919673457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104536494998490997946448971 156804742497736496919673457)
  ·
    refine ⟨117603556873302372689755093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156804742497736496919673457 117603556873302372689755093)
    ·
      refine ⟨2756333364218024359916135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 117603556873302372689755093 2756333364218024359916135)
      ·
        refine ⟨4134500046327036539874203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756333364218024359916135 4134500046327036539874203)
        ·
          refine ⟨6201750069490554809811305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134500046327036539874203 6201750069490554809811305)
          ·
            refine ⟨4651312552117916107358479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6201750069490554809811305 4651312552117916107358479)
            ·
              refine ⟨6976968828176874161037719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651312552117916107358479 6976968828176874161037719)
              ·
                refine ⟨10465453242265311241556579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6976968828176874161037719 10465453242265311241556579)
                ·
                  refine ⟨15698179863397966862334869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10465453242265311241556579 15698179863397966862334869)
                  ·
                    refine ⟨735852181096779696671947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15698179863397966862334869 735852181096779696671947)
                    ·
                      rfl

theorem cell23_4299201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4299201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299201 prefixEnd_4299201 := by exact prefixLift 4299201
  have htrace : WordTrace (prefixWord ++ tailWord_4299201) baseStart_4299201 baseEnd_4299201 := by
    simpa [prefixWord, tailWord_4299201, baseEnd_4299201] using wordTrace_append hprefix tailTrace_4299201
  have hstable : (prefixWord ++ tailWord_4299201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299201).length < 2 ^ (prefixWord ++ tailWord_4299201).sum := by decide
  have hdescent : baseEnd_4299201 < baseStart_4299201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299204 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4299204 : Nat := 118140960795 + 4299204 * 2 ^ 59
def prefixEnd_4299204 : Nat := 4983230072969 + 3 ^ 40 * 4299204 * 2
def baseEnd_4299204 : Nat := 2207558083732302578278327

theorem tailTrace_4299204 : CollatzResearch.WordTrace tailWord_4299204 prefixEnd_4299204 2207558083732302578278327 := by
  unfold tailWord_4299204
  simp only [CollatzResearch.WordTrace]
  refine ⟨78402425958362814216016333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104536567944483752288021777 78402425958362814216016333)
  ·
    refine ⟨29400909734386055331006125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78402425958362814216016333 29400909734386055331006125)
    ·
      refine ⟨11025341150394770749127297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29400909734386055331006125 11025341150394770749127297)
      ·
        refine ⟨8269005862796078061845473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11025341150394770749127297 8269005862796078061845473)
        ·
          refine ⟨6201754397097058546384105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8269005862796078061845473 6201754397097058546384105)
          ·
            refine ⟨4651315797822793909788079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6201754397097058546384105 4651315797822793909788079)
            ·
              refine ⟨6976973696734190864682119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651315797822793909788079 6976973696734190864682119)
              ·
                refine ⟨10465460545101286297023179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6976973696734190864682119 10465460545101286297023179)
                ·
                  refine ⟨15698190817651929445534769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10465460545101286297023179 15698190817651929445534769)
                  ·
                    refine ⟨11773643113238947084151077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15698190817651929445534769 11773643113238947084151077)
                    ·
                      refine ⟨2207558083732302578278327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11773643113238947084151077 2207558083732302578278327)
                      ·
                        rfl

theorem cell23_4299204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4299204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299204 prefixEnd_4299204 := by exact prefixLift 4299204
  have htrace : WordTrace (prefixWord ++ tailWord_4299204) baseStart_4299204 baseEnd_4299204 := by
    simpa [prefixWord, tailWord_4299204, baseEnd_4299204] using wordTrace_append hprefix tailTrace_4299204
  have hstable : (prefixWord ++ tailWord_4299204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299204).length < 2 ^ (prefixWord ++ tailWord_4299204).sum := by decide
  have hdescent : baseEnd_4299204 < baseStart_4299204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299207 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_4299207 : Nat := 118140960795 + 4299207 * 2 ^ 59
def prefixEnd_4299207 : Nat := 4983230072969 + 3 ^ 40 * 4299207 * 2
def baseEnd_4299207 : Nat := 2207559624174266066540813

theorem tailTrace_4299207 : CollatzResearch.WordTrace tailWord_4299207 prefixEnd_4299207 2207559624174266066540813 := by
  unfold tailWord_4299207
  simp only [CollatzResearch.WordTrace]
  refine ⟨156804961335714759944391875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104536640890476506629594583 156804961335714759944391875)
  ·
    refine ⟨235207442003572139916587813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156804961335714759944391875 235207442003572139916587813)
    ·
      refine ⟨44101395375669776234360215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235207442003572139916587813 44101395375669776234360215)
      ·
        refine ⟨66152093063504664351540323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44101395375669776234360215 66152093063504664351540323)
        ·
          refine ⟨99228139595256996527310485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66152093063504664351540323 99228139595256996527310485)
          ·
            refine ⟨4651319043527671712217679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99228139595256996527310485 4651319043527671712217679)
            ·
              refine ⟨6976978565291507568326519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651319043527671712217679 6976978565291507568326519)
              ·
                refine ⟨10465467847937261352489779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6976978565291507568326519 10465467847937261352489779)
                ·
                  refine ⟨15698201771905892028734669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10465467847937261352489779 15698201771905892028734669)
                  ·
                    refine ⟨5886825664464709510775501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15698201771905892028734669 5886825664464709510775501)
                    ·
                      refine ⟨2207559624174266066540813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5886825664464709510775501 2207559624174266066540813)
                      ·
                        rfl

theorem cell23_4299207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_4299207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299207 prefixEnd_4299207 := by exact prefixLift 4299207
  have htrace : WordTrace (prefixWord ++ tailWord_4299207) baseStart_4299207 baseEnd_4299207 := by
    simpa [prefixWord, tailWord_4299207, baseEnd_4299207] using wordTrace_append hprefix tailTrace_4299207
  have hstable : (prefixWord ++ tailWord_4299207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299207).length < 2 ^ (prefixWord ++ tailWord_4299207).sum := by decide
  have hdescent : baseEnd_4299207 < baseStart_4299207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299220 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4299220 : Nat := 118140960795 + 4299220 * 2 ^ 59
def prefixEnd_4299220 : Nat := 4983230072969 + 3 ^ 40 * 4299220 * 2
def baseEnd_4299220 : Nat := 2207566299422774515678253

theorem tailTrace_4299220 : CollatzResearch.WordTrace tailWord_4299220 prefixEnd_4299220 2207566299422774515678253 := by
  unfold tailWord_4299220
  simp only [CollatzResearch.WordTrace]
  refine ⟨78402717742333831582307557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104536956989778442109743409 78402717742333831582307557)
  ·
    refine ⟨14700509576687593421682667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78402717742333831582307557 14700509576687593421682667)
    ·
      refine ⟨22050764365031390132524001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14700509576687593421682667 22050764365031390132524001)
      ·
        refine ⟨16538073273773542599393001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22050764365031390132524001 16538073273773542599393001)
        ·
          refine ⟨12403554955330156949544751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16538073273773542599393001 12403554955330156949544751)
          ·
            refine ⟨18605332432995235424317127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12403554955330156949544751 18605332432995235424317127)
            ·
              refine ⟨27907998649492853136475691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18605332432995235424317127 27907998649492853136475691)
              ·
                refine ⟨41861997974239279704713537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27907998649492853136475691 41861997974239279704713537)
                ·
                  refine ⟨31396498480679459778535153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41861997974239279704713537 31396498480679459778535153)
                  ·
                    refine ⟨23547373860509594833901365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31396498480679459778535153 23547373860509594833901365)
                    ·
                      refine ⟨2207566299422774515678253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23547373860509594833901365 2207566299422774515678253)
                      ·
                        rfl

theorem cell23_4299220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4299220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299220 prefixEnd_4299220 := by exact prefixLift 4299220
  have htrace : WordTrace (prefixWord ++ tailWord_4299220) baseStart_4299220 baseEnd_4299220 := by
    simpa [prefixWord, tailWord_4299220, baseEnd_4299220] using wordTrace_append hprefix tailTrace_4299220
  have hstable : (prefixWord ++ tailWord_4299220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299220).length < 2 ^ (prefixWord ++ tailWord_4299220).sum := by decide
  have hdescent : baseEnd_4299220 < baseStart_4299220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299304 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 5]
def baseStart_4299304 : Nat := 118140960795 + 4299304 * 2 ^ 59
def prefixEnd_4299304 : Nat := 4983230072969 + 3 ^ 40 * 4299304 * 2
def baseEnd_4299304 : Nat := 245289936866416909669763

theorem tailTrace_4299304 : CollatzResearch.WordTrace tailWord_4299304 prefixEnd_4299304 245289936866416909669763 := by
  unfold tailWord_4299304
  simp only [CollatzResearch.WordTrace]
  refine ⟨78404249608181672755336483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104538999477575563673781977 78404249608181672755336483)
  ·
    refine ⟨117606374412272509133004725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78404249608181672755336483 117606374412272509133004725)
    ·
      refine ⟨11025597601150547731219193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117606374412272509133004725 11025597601150547731219193)
      ·
        refine ⟨8269198200862910798414395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11025597601150547731219193 8269198200862910798414395)
        ·
          refine ⟨12403797301294366197621593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8269198200862910798414395 12403797301294366197621593)
          ·
            refine ⟨9302847975970774648216195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12403797301294366197621593 9302847975970774648216195)
            ·
              refine ⟨13954271963956161972324293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9302847975970774648216195 13954271963956161972324293)
              ·
                refine ⟨2616425993241780369810805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13954271963956161972324293 2616425993241780369810805)
                ·
                  refine ⟨245289936866416909669763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2616425993241780369810805 245289936866416909669763)
                  ·
                    rfl

theorem cell23_4299304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 5].length) (baseStart_4299304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299304 prefixEnd_4299304 := by exact prefixLift 4299304
  have htrace : WordTrace (prefixWord ++ tailWord_4299304) baseStart_4299304 baseEnd_4299304 := by
    simpa [prefixWord, tailWord_4299304, baseEnd_4299304] using wordTrace_append hprefix tailTrace_4299304
  have hstable : (prefixWord ++ tailWord_4299304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299304).length < 2 ^ (prefixWord ++ tailWord_4299304).sum := by decide
  have hdescent : baseEnd_4299304 < baseStart_4299304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299320 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_4299320 : Nat := 118140960795 + 4299320 * 2 ^ 59
def prefixEnd_4299320 : Nat := 4983230072969 + 3 ^ 40 * 4299320 * 2
def baseEnd_4299320 : Nat := 2207617647488224124427793

theorem tailTrace_4299320 : CollatzResearch.WordTrace tailWord_4299320 prefixEnd_4299320 2207617647488224124427793 := by
  unfold tailWord_4299320
  simp only [CollatzResearch.WordTrace]
  refine ⟨78404541392152690121627707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104539388522870253495503609 78404541392152690121627707)
  ·
    refine ⟨117606812088229035182441561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78404541392152690121627707 117606812088229035182441561)
    ·
      refine ⟨88205109066171776386831171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117606812088229035182441561 88205109066171776386831171)
      ·
        refine ⟨132307663599257664580246757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88205109066171776386831171 132307663599257664580246757)
        ·
          refine ⟨24807686924860812108796267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132307663599257664580246757 24807686924860812108796267)
          ·
            refine ⟨37211530387291218163194401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24807686924860812108796267 37211530387291218163194401)
            ·
              refine ⟨27908647790468413622395801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37211530387291218163194401 27908647790468413622395801)
              ·
                refine ⟨20931485842851310216796851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27908647790468413622395801 20931485842851310216796851)
                ·
                  refine ⟨31397228764276965325195277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20931485842851310216796851 31397228764276965325195277)
                  ·
                    refine ⟨11773960786603861996948229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31397228764276965325195277 11773960786603861996948229)
                    ·
                      refine ⟨2207617647488224124427793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11773960786603861996948229 2207617647488224124427793)
                      ·
                        rfl

theorem cell23_4299320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_4299320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299320 prefixEnd_4299320 := by exact prefixLift 4299320
  have htrace : WordTrace (prefixWord ++ tailWord_4299320) baseStart_4299320 baseEnd_4299320 := by
    simpa [prefixWord, tailWord_4299320, baseEnd_4299320] using wordTrace_append hprefix tailTrace_4299320
  have hstable : (prefixWord ++ tailWord_4299320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299320).length < 2 ^ (prefixWord ++ tailWord_4299320).sum := by decide
  have hdescent : baseEnd_4299320 < baseStart_4299320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299334 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4299334 : Nat := 118140960795 + 4299334 * 2 ^ 59
def prefixEnd_4299334 : Nat := 4983230072969 + 3 ^ 40 * 4299334 * 2
def baseEnd_4299334 : Nat := 735874945405795689884243

theorem tailTrace_4299334 : CollatzResearch.WordTrace tailWord_4299334 prefixEnd_4299334 735874945405795689884243 := by
  unfold tailWord_4299334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900299793945458144820783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104539728937503107089510037 4900299793945458144820783)
  ·
    refine ⟨7350449690918187217231175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4900299793945458144820783 7350449690918187217231175)
    ·
      refine ⟨11025674536377280825846763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7350449690918187217231175 11025674536377280825846763)
      ·
        refine ⟨16538511804565921238770145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11025674536377280825846763 16538511804565921238770145)
        ·
          refine ⟨12403883853424440929077609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16538511804565921238770145 12403883853424440929077609)
          ·
            refine ⟨9302912890068330696808207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12403883853424440929077609 9302912890068330696808207)
            ·
              refine ⟨13954369335102496045212311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9302912890068330696808207 13954369335102496045212311)
              ·
                refine ⟨20931554002653744067818467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13954369335102496045212311 20931554002653744067818467)
                ·
                  refine ⟨31397331003980616101727701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20931554002653744067818467 31397331003980616101727701)
                  ·
                    refine ⟨735874945405795689884243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31397331003980616101727701 735874945405795689884243)
                    ·
                      rfl

theorem cell23_4299334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4299334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299334 prefixEnd_4299334 := by exact prefixLift 4299334
  have htrace : WordTrace (prefixWord ++ tailWord_4299334) baseStart_4299334 baseEnd_4299334 := by
    simpa [prefixWord, tailWord_4299334, baseEnd_4299334] using wordTrace_append hprefix tailTrace_4299334
  have hstable : (prefixWord ++ tailWord_4299334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299334).length < 2 ^ (prefixWord ++ tailWord_4299334).sum := by decide
  have hdescent : baseEnd_4299334 < baseStart_4299334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299364 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_4299364 : Nat := 118140960795 + 4299364 * 2 ^ 59
def prefixEnd_4299364 : Nat := 4983230072969 + 3 ^ 40 * 4299364 * 2
def baseEnd_4299364 : Nat := 735880080212340650759197

theorem tailTrace_4299364 : CollatzResearch.WordTrace tailWord_4299364 prefixEnd_4299364 735880080212340650759197 := by
  unfold tailWord_4299364
  simp only [CollatzResearch.WordTrace]
  refine ⟨78405343798072987878928573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104540458397430650505238097 78405343798072987878928573)
  ·
    refine ⟨29402003924277370454598215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78405343798072987878928573 29402003924277370454598215)
    ·
      refine ⟨44103005886416055681897323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29402003924277370454598215 44103005886416055681897323)
      ·
        refine ⟨66154508829624083522845985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44103005886416055681897323 66154508829624083522845985)
        ·
          refine ⟨49615881622218062642134489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66154508829624083522845985 49615881622218062642134489)
          ·
            refine ⟨37211911216663546981600867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49615881622218062642134489 37211911216663546981600867)
            ·
              refine ⟨55817866824995320472401301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37211911216663546981600867 55817866824995320472401301)
              ·
                refine ⟨2616462507421655647143811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55817866824995320472401301 2616462507421655647143811)
                ·
                  refine ⟨3924693761132483470715717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616462507421655647143811 3924693761132483470715717)
                  ·
                    refine ⟨735880080212340650759197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3924693761132483470715717 735880080212340650759197)
                    ·
                      rfl

theorem cell23_4299364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_4299364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299364 prefixEnd_4299364 := by exact prefixLift 4299364
  have htrace : WordTrace (prefixWord ++ tailWord_4299364) baseStart_4299364 baseEnd_4299364 := by
    simpa [prefixWord, tailWord_4299364, baseEnd_4299364] using wordTrace_append hprefix tailTrace_4299364
  have hstable : (prefixWord ++ tailWord_4299364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299364).length < 2 ^ (prefixWord ++ tailWord_4299364).sum := by decide
  have hdescent : baseEnd_4299364 < baseStart_4299364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299387 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 3]
def baseStart_4299387 : Nat := 118140960795 + 4299387 * 2 ^ 59
def prefixEnd_4299387 : Nat := 4983230072969 + 3 ^ 40 * 4299387 * 2
def baseEnd_4299387 : Nat := 2207652050692075362289985

theorem tailTrace_4299387 : CollatzResearch.WordTrace tailWord_4299387 prefixEnd_4299387 2207652050692075362289985 := by
  unfold tailWord_4299387
  simp only [CollatzResearch.WordTrace]
  refine ⟨156811526475062650685944415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104541017650041767123962943 156811526475062650685944415)
  ·
    refine ⟨235217289712593976028916623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156811526475062650685944415 235217289712593976028916623)
    ·
      refine ⟨352825934568890964043374935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235217289712593976028916623 352825934568890964043374935)
      ·
        refine ⟨529238901853336446065062403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352825934568890964043374935 529238901853336446065062403)
        ·
          refine ⟨793858352780004669097593605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529238901853336446065062403 793858352780004669097593605)
          ·
            refine ⟨148848441146250875455798801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 793858352780004669097593605 148848441146250875455798801)
            ·
              refine ⟨111636330859688156591849101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148848441146250875455798801 111636330859688156591849101)
              ·
                refine ⟨41863624072383058721943413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111636330859688156591849101 41863624072383058721943413)
                ·
                  refine ⟨3924714756785911755182195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41863624072383058721943413 3924714756785911755182195)
                  ·
                    refine ⟨5887072135178867632773293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3924714756785911755182195 5887072135178867632773293)
                    ·
                      refine ⟨2207652050692075362289985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5887072135178867632773293 2207652050692075362289985)
                      ·
                        rfl

theorem cell23_4299387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 3].length) (baseStart_4299387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299387 prefixEnd_4299387 := by exact prefixLift 4299387
  have htrace : WordTrace (prefixWord ++ tailWord_4299387) baseStart_4299387 baseEnd_4299387 := by
    simpa [prefixWord, tailWord_4299387, baseEnd_4299387] using wordTrace_append hprefix tailTrace_4299387
  have hstable : (prefixWord ++ tailWord_4299387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299387).length < 2 ^ (prefixWord ++ tailWord_4299387).sum := by decide
  have hdescent : baseEnd_4299387 < baseStart_4299387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299421 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_4299421 : Nat := 118140960795 + 4299421 * 2 ^ 59
def prefixEnd_4299421 : Nat := 4983230072969 + 3 ^ 40 * 4299421 * 2
def baseEnd_4299421 : Nat := 2207669509034328229264829

theorem tailTrace_4299421 : CollatzResearch.WordTrace tailWord_4299421 prefixEnd_4299421 2207669509034328229264829 := by
  unfold tailWord_4299421
  simp only [CollatzResearch.WordTrace]
  refine ⟨156812766556939474492682117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104541844371292982995121411 156812766556939474492682117)
  ·
    refine ⟨29402393729426151467377897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156812766556939474492682117 29402393729426151467377897)
    ·
      refine ⟨22051795297069613600533423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29402393729426151467377897 22051795297069613600533423)
      ·
        refine ⟨33077692945604420400800135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22051795297069613600533423 33077692945604420400800135)
        ·
          refine ⟨49616539418406630601200203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33077692945604420400800135 49616539418406630601200203)
          ·
            refine ⟨74424809127609945901800305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49616539418406630601200203 74424809127609945901800305)
            ·
              refine ⟨55818606845707459426350229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74424809127609945901800305 55818606845707459426350229)
              ·
                refine ⟨2616497195892537160610167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55818606845707459426350229 2616497195892537160610167)
                ·
                  refine ⟨3924745793838805740915251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616497195892537160610167 3924745793838805740915251)
                  ·
                    refine ⟨5887118690758208611372877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3924745793838805740915251 5887118690758208611372877)
                    ·
                      refine ⟨2207669509034328229264829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5887118690758208611372877 2207669509034328229264829)
                      ·
                        rfl

theorem cell23_4299421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_4299421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299421 prefixEnd_4299421 := by exact prefixLift 4299421
  have htrace : WordTrace (prefixWord ++ tailWord_4299421) baseStart_4299421 baseEnd_4299421 := by
    simpa [prefixWord, tailWord_4299421, baseEnd_4299421] using wordTrace_append hprefix tailTrace_4299421
  have hstable : (prefixWord ++ tailWord_4299421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299421).length < 2 ^ (prefixWord ++ tailWord_4299421).sum := by decide
  have hdescent : baseEnd_4299421 < baseStart_4299421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299427 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 6, 2]
def baseStart_4299427 : Nat := 118140960795 + 4299427 * 2 ^ 59
def prefixEnd_4299427 : Nat := 4983230072969 + 3 ^ 40 * 4299427 * 2
def baseEnd_4299427 : Nat := 2207672589918255205789801

theorem tailTrace_4299427 : CollatzResearch.WordTrace tailWord_4299427 prefixEnd_4299427 2207672589918255205789801 := by
  unfold tailWord_4299427
  simp only [CollatzResearch.WordTrace]
  refine ⟨156812985394917737517400535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104541990263278491678267023 156812985394917737517400535)
  ·
    refine ⟨235219478092376606276100803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156812985394917737517400535 235219478092376606276100803)
    ·
      refine ⟨352829217138564909414151205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235219478092376606276100803 352829217138564909414151205)
      ·
        refine ⟨66155478213480920515153351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 352829217138564909414151205 66155478213480920515153351)
        ·
          refine ⟨99233217320221380772730027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66155478213480920515153351 99233217320221380772730027)
          ·
            refine ⟨148849825980332071159095041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99233217320221380772730027 148849825980332071159095041)
            ·
              refine ⟨111637369485249053369321281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148849825980332071159095041 111637369485249053369321281)
              ·
                refine ⟨83728027113936790026990961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111637369485249053369321281 83728027113936790026990961)
                ·
                  refine ⟨62796020335452592520243221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83728027113936790026990961 62796020335452592520243221)
                  ·
                    refine ⟨2943563453224340274386401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62796020335452592520243221 2943563453224340274386401)
                    ·
                      refine ⟨2207672589918255205789801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943563453224340274386401 2207672589918255205789801)
                      ·
                        rfl

theorem cell23_4299427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_4299427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299427 prefixEnd_4299427 := by exact prefixLift 4299427
  have htrace : WordTrace (prefixWord ++ tailWord_4299427) baseStart_4299427 baseEnd_4299427 := by
    simpa [prefixWord, tailWord_4299427, baseEnd_4299427] using wordTrace_append hprefix tailTrace_4299427
  have hstable : (prefixWord ++ tailWord_4299427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299427).length < 2 ^ (prefixWord ++ tailWord_4299427).sum := by decide
  have hdescent : baseEnd_4299427 < baseStart_4299427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299450 : List Nat := [3, 1, 1, 1, 2, 3, 1, 11]
def baseStart_4299450 : Nat := 118140960795 + 4299450 * 2 ^ 59
def prefixEnd_4299450 : Nat := 4983230072969 + 3 ^ 40 * 4299450 * 2
def baseEnd_4299450 : Nat := 81766088887900319103785

theorem tailTrace_4299450 : CollatzResearch.WordTrace tailWord_4299450 prefixEnd_4299450 81766088887900319103785 := by
  unfold tailWord_4299450
  simp only [CollatzResearch.WordTrace]
  refine ⟨39203456068458603111371951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104542549515889608296991869 39203456068458603111371951)
  ·
    refine ⟨58805184102687904667057927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39203456068458603111371951 58805184102687904667057927)
    ·
      refine ⟨88207776154031857000586891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58805184102687904667057927 88207776154031857000586891)
      ·
        refine ⟨132311664231047785500880337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88207776154031857000586891 132311664231047785500880337)
        ·
          refine ⟨99233748173285839125660253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132311664231047785500880337 99233748173285839125660253)
          ·
            refine ⟨37212655564982189672122595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99233748173285839125660253 37212655564982189672122595)
            ·
              refine ⟨55818983347473284508183893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37212655564982189672122595 55818983347473284508183893)
              ·
                refine ⟨81766088887900319103785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55818983347473284508183893 81766088887900319103785)
                ·
                  rfl

theorem cell23_4299450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_4299450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299450 prefixEnd_4299450 := by exact prefixLift 4299450
  have htrace : WordTrace (prefixWord ++ tailWord_4299450) baseStart_4299450 baseEnd_4299450 := by
    simpa [prefixWord, tailWord_4299450, baseEnd_4299450] using wordTrace_append hprefix tailTrace_4299450
  have hstable : (prefixWord ++ tailWord_4299450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299450).length < 2 ^ (prefixWord ++ tailWord_4299450).sum := by decide
  have hdescent : baseEnd_4299450 < baseStart_4299450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299464 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_4299464 : Nat := 118140960795 + 4299464 * 2 ^ 59
def prefixEnd_4299464 : Nat := 4983230072969 + 3 ^ 40 * 4299464 * 2
def baseEnd_4299464 : Nat := 2207691588702471561027131

theorem tailTrace_4299464 : CollatzResearch.WordTrace tailWord_4299464 prefixEnd_4299464 2207691588702471561027131 := by
  unfold tailWord_4299464
  simp only [CollatzResearch.WordTrace]
  refine ⟨78407167447891846418248723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104542889930522461890998297 78407167447891846418248723)
  ·
    refine ⟨117610751171837769627373085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78407167447891846418248723 117610751171837769627373085)
    ·
      refine ⟨44104031689439163610264907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117610751171837769627373085 44104031689439163610264907)
      ·
        refine ⟨66156047534158745415397361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44104031689439163610264907 66156047534158745415397361)
        ·
          refine ⟨49617035650619059061548021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66156047534158745415397361 49617035650619059061548021)
          ·
            refine ⟨4651597092245536787020127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49617035650619059061548021 4651597092245536787020127)
            ·
              refine ⟨6977395638368305180530191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651597092245536787020127 6977395638368305180530191)
              ·
                refine ⟨10466093457552457770795287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977395638368305180530191 10466093457552457770795287)
                ·
                  refine ⟨15699140186328686656192931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10466093457552457770795287 15699140186328686656192931)
                  ·
                    refine ⟨23548710279493029984289397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15699140186328686656192931 23548710279493029984289397)
                    ·
                      refine ⟨2207691588702471561027131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23548710279493029984289397 2207691588702471561027131)
                      ·
                        rfl

theorem cell23_4299464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_4299464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299464 prefixEnd_4299464 := by exact prefixLift 4299464
  have htrace : WordTrace (prefixWord ++ tailWord_4299464) baseStart_4299464 baseEnd_4299464 := by
    simpa [prefixWord, tailWord_4299464, baseEnd_4299464] using wordTrace_append hprefix tailTrace_4299464
  have hstable : (prefixWord ++ tailWord_4299464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299464).length < 2 ^ (prefixWord ++ tailWord_4299464).sum := by decide
  have hdescent : baseEnd_4299464 < baseStart_4299464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299484 : List Nat := [2, 2, 5, 1, 1, 1, 3, 8]
def baseStart_4299484 : Nat := 118140960795 + 4299484 * 2 ^ 59
def prefixEnd_4299484 : Nat := 4983230072969 + 3 ^ 40 * 4299484 * 2
def baseEnd_4299484 : Nat := 81766735493168943806557

theorem tailTrace_4299484 : CollatzResearch.WordTrace tailWord_4299484 prefixEnd_4299484 81766735493168943806557 := by
  unfold tailWord_4299484
  simp only [CollatzResearch.WordTrace]
  refine ⟨78407532177855618126112753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104543376237140824168150337 78407532177855618126112753)
  ·
    refine ⟨58805649133391713594584565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78407532177855618126112753 58805649133391713594584565)
    ·
      refine ⟨5513029606255473149492303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58805649133391713594584565 5513029606255473149492303)
      ·
        refine ⟨8269544409383209724238455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5513029606255473149492303 8269544409383209724238455)
        ·
          refine ⟨12404316614074814586357683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8269544409383209724238455 12404316614074814586357683)
          ·
            refine ⟨18606474921112221879536525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12404316614074814586357683 18606474921112221879536525)
            ·
              refine ⟨6977428095417083204826197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18606474921112221879536525 6977428095417083204826197)
              ·
                refine ⟨81766735493168943806557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6977428095417083204826197 81766735493168943806557)
                ·
                  rfl

theorem cell23_4299484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 8].length) (baseStart_4299484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299484 prefixEnd_4299484 := by exact prefixLift 4299484
  have htrace : WordTrace (prefixWord ++ tailWord_4299484) baseStart_4299484 baseEnd_4299484 := by
    simpa [prefixWord, tailWord_4299484, baseEnd_4299484] using wordTrace_append hprefix tailTrace_4299484
  have hstable : (prefixWord ++ tailWord_4299484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299484).length < 2 ^ (prefixWord ++ tailWord_4299484).sum := by decide
  have hdescent : baseEnd_4299484 < baseStart_4299484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299504 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 3, 3, 2]
def baseStart_4299504 : Nat := 118140960795 + 4299504 * 2 ^ 59
def prefixEnd_4299504 : Nat := 4983230072969 + 3 ^ 40 * 4299504 * 2
def baseEnd_4299504 : Nat := 2207712127928651404526947

theorem tailTrace_4299504 : CollatzResearch.WordTrace tailWord_4299504 prefixEnd_4299504 2207712127928651404526947 := by
  unfold tailWord_4299504
  simp only [CollatzResearch.WordTrace]
  refine ⟨78407896907819389833976783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104543862543759186445302377 78407896907819389833976783)
  ·
    refine ⟨117611845361729084750965175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78407896907819389833976783 117611845361729084750965175)
    ·
      refine ⟨176417768042593627126447763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117611845361729084750965175 176417768042593627126447763)
      ·
        refine ⟨264626652063890440689671645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176417768042593627126447763 264626652063890440689671645)
        ·
          refine ⟨99234994523958915258626867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264626652063890440689671645 99234994523958915258626867)
          ·
            refine ⟨148852491785938372887940301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99234994523958915258626867 148852491785938372887940301)
            ·
              refine ⟨55819684419726889832977613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148852491785938372887940301 55819684419726889832977613)
              ·
                refine ⟨20932381657397583687366605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55819684419726889832977613 20932381657397583687366605)
                ·
                  refine ⟨7849643121524093882762477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20932381657397583687366605 7849643121524093882762477)
                  ·
                    refine ⟨2943616170571535206035929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7849643121524093882762477 2943616170571535206035929)
                    ·
                      refine ⟨2207712127928651404526947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943616170571535206035929 2207712127928651404526947)
                      ·
                        rfl

theorem cell23_4299504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 3, 2].length) (baseStart_4299504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299504 prefixEnd_4299504 := by exact prefixLift 4299504
  have htrace : WordTrace (prefixWord ++ tailWord_4299504) baseStart_4299504 baseEnd_4299504 := by
    simpa [prefixWord, tailWord_4299504, baseEnd_4299504] using wordTrace_append hprefix tailTrace_4299504
  have hstable : (prefixWord ++ tailWord_4299504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299504).length < 2 ^ (prefixWord ++ tailWord_4299504).sum := by decide
  have hdescent : baseEnd_4299504 < baseStart_4299504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299528 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_4299528 : Nat := 118140960795 + 4299528 * 2 ^ 59
def prefixEnd_4299528 : Nat := 4983230072969 + 3 ^ 40 * 4299528 * 2
def baseEnd_4299528 : Nat := 2207724451464359310626837

theorem tailTrace_4299528 : CollatzResearch.WordTrace tailWord_4299528 prefixEnd_4299528 2207724451464359310626837 := by
  unfold tailWord_4299528
  simp only [CollatzResearch.WordTrace]
  refine ⟨78408334583775915883413619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104544446111701221177884825 78408334583775915883413619)
  ·
    refine ⟨117612501875663873825120429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78408334583775915883413619 117612501875663873825120429)
    ·
      refine ⟨44104688203373952684420161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117612501875663873825120429 44104688203373952684420161)
      ·
        refine ⟨33078516152530464513315121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44104688203373952684420161 33078516152530464513315121)
        ·
          refine ⟨24808887114397848384986341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33078516152530464513315121 24808887114397848384986341)
          ·
            refine ⟨4651666333949596572184939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24808887114397848384986341 4651666333949596572184939)
            ·
              refine ⟨6977499500924394858277409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651666333949596572184939 6977499500924394858277409)
              ·
                refine ⟨5233124625693296143708057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6977499500924394858277409 5233124625693296143708057)
                ·
                  refine ⟨3924843469269972107781043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5233124625693296143708057 3924843469269972107781043)
                  ·
                    refine ⟨5887265203904958161671565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3924843469269972107781043 5887265203904958161671565)
                    ·
                      refine ⟨2207724451464359310626837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5887265203904958161671565 2207724451464359310626837)
                      ·
                        rfl

theorem cell23_4299528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_4299528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299528 prefixEnd_4299528 := by exact prefixLift 4299528
  have htrace : WordTrace (prefixWord ++ tailWord_4299528) baseStart_4299528 baseEnd_4299528 := by
    simpa [prefixWord, tailWord_4299528, baseEnd_4299528] using wordTrace_append hprefix tailTrace_4299528
  have hstable : (prefixWord ++ tailWord_4299528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299528).length < 2 ^ (prefixWord ++ tailWord_4299528).sum := by decide
  have hdescent : baseEnd_4299528 < baseStart_4299528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299537 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_4299537 : Nat := 118140960795 + 4299537 * 2 ^ 59
def prefixEnd_4299537 : Nat := 4983230072969 + 3 ^ 40 * 4299537 * 2
def baseEnd_4299537 : Nat := 2207729072790249775414295

theorem tailTrace_4299537 : CollatzResearch.WordTrace tailWord_4299537 prefixEnd_4299537 2207729072790249775414295 := by
  unfold tailWord_4299537
  simp only [CollatzResearch.WordTrace]
  refine ⟨156816997424519226303904865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104544664949679484202603243 156816997424519226303904865)
  ·
    refine ⟨117612748068389419727928649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156816997424519226303904865 117612748068389419727928649)
    ·
      refine ⟨88209561051292064795946487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117612748068389419727928649 88209561051292064795946487)
      ·
        refine ⟨132314341576938097193919731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88209561051292064795946487 132314341576938097193919731)
        ·
          refine ⟨198471512365407145790879597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132314341576938097193919731 198471512365407145790879597)
          ·
            refine ⟨74426817137027679671579849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198471512365407145790879597 74426817137027679671579849)
            ·
              refine ⟨55820112852770759753684887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74426817137027679671579849 55820112852770759753684887)
              ·
                refine ⟨83730169279156139630527331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55820112852770759753684887 83730169279156139630527331)
                ·
                  refine ⟨125595253918734209445790997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83730169279156139630527331 125595253918734209445790997)
                  ·
                    refine ⟨5887277527440666067771453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125595253918734209445790997 5887277527440666067771453)
                    ·
                      refine ⟨2207729072790249775414295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5887277527440666067771453 2207729072790249775414295)
                      ·
                        rfl

theorem cell23_4299537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_4299537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299537 prefixEnd_4299537 := by exact prefixLift 4299537
  have htrace : WordTrace (prefixWord ++ tailWord_4299537) baseStart_4299537 baseEnd_4299537 := by
    simpa [prefixWord, tailWord_4299537, baseEnd_4299537] using wordTrace_append hprefix tailTrace_4299537
  have hstable : (prefixWord ++ tailWord_4299537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299537).length < 2 ^ (prefixWord ++ tailWord_4299537).sum := by decide
  have hdescent : baseEnd_4299537 < baseStart_4299537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299551 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 1, 4, 2]
def baseStart_4299551 : Nat := 118140960795 + 4299551 * 2 ^ 59
def prefixEnd_4299551 : Nat := 4983230072969 + 3 ^ 40 * 4299551 * 2
def baseEnd_4299551 : Nat := 2207736261519412720639231

theorem tailTrace_4299551 : CollatzResearch.WordTrace tailWord_4299551 prefixEnd_4299551 2207736261519412720639231 := by
  unfold tailWord_4299551
  simp only [CollatzResearch.WordTrace]
  refine ⟨156817508046468506694914507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104545005364312337796609671 156817508046468506694914507)
  ·
    refine ⟨235226262069702760042371761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156817508046468506694914507 235226262069702760042371761)
    ·
      refine ⟨176419696552277070031778821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235226262069702760042371761 176419696552277070031778821)
      ·
        refine ⟨33078693103551950630958529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176419696552277070031778821 33078693103551950630958529)
        ·
          refine ⟨24809019827663962973218897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33078693103551950630958529 24809019827663962973218897)
          ·
            refine ⟨18606764870747972229914173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24809019827663962973218897 18606764870747972229914173)
            ·
              refine ⟨6977536826530489586217815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18606764870747972229914173 6977536826530489586217815)
              ·
                refine ⟨10466305239795734379326723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977536826530489586217815 10466305239795734379326723)
                ·
                  refine ⟨15699457859693601568990085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10466305239795734379326723 15699457859693601568990085)
                  ·
                    refine ⟨2943648348692550294185641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15699457859693601568990085 2943648348692550294185641)
                    ·
                      refine ⟨2207736261519412720639231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943648348692550294185641 2207736261519412720639231)
                      ·
                        rfl

theorem cell23_4299551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_4299551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299551 prefixEnd_4299551 := by exact prefixLift 4299551
  have htrace : WordTrace (prefixWord ++ tailWord_4299551) baseStart_4299551 baseEnd_4299551 := by
    simpa [prefixWord, tailWord_4299551, baseEnd_4299551] using wordTrace_append hprefix tailTrace_4299551
  have hstable : (prefixWord ++ tailWord_4299551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299551).length < 2 ^ (prefixWord ++ tailWord_4299551).sum := by decide
  have hdescent : baseEnd_4299551 < baseStart_4299551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299557 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 7]
def baseStart_4299557 : Nat := 118140960795 + 4299557 * 2 ^ 59
def prefixEnd_4299557 : Nat := 4983230072969 + 3 ^ 40 * 4299557 * 2
def baseEnd_4299557 : Nat := 245304371378148855240467

theorem tailTrace_4299557 : CollatzResearch.WordTrace tailWord_4299557 prefixEnd_4299557 245304371378148855240467 := by
  unfold tailWord_4299557
  simp only [CollatzResearch.WordTrace]
  refine ⟨156817726884446769719632925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104545151256297846479755283 156817726884446769719632925)
  ·
    refine ⟨58806647581667538644862347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156817726884446769719632925 58806647581667538644862347)
    ·
      refine ⟨88209971372501307967293521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58806647581667538644862347 88209971372501307967293521)
      ·
        refine ⟨66157478529375980975470141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88209971372501307967293521 66157478529375980975470141)
        ·
          refine ⟨24809054448515992865801303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66157478529375980975470141 24809054448515992865801303)
          ·
            refine ⟨37213581672773989298701955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24809054448515992865801303 37213581672773989298701955)
            ·
              refine ⟨55820372509160983948052933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37213581672773989298701955 55820372509160983948052933)
              ·
                refine ⟨10466319845467684490259925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55820372509160983948052933 10466319845467684490259925)
                ·
                  refine ⟨245304371378148855240467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10466319845467684490259925 245304371378148855240467)
                  ·
                    rfl

theorem cell23_4299557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_4299557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299557 prefixEnd_4299557 := by exact prefixLift 4299557
  have htrace : WordTrace (prefixWord ++ tailWord_4299557) baseStart_4299557 baseEnd_4299557 := by
    simpa [prefixWord, tailWord_4299557, baseEnd_4299557] using wordTrace_append hprefix tailTrace_4299557
  have hstable : (prefixWord ++ tailWord_4299557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299557).length < 2 ^ (prefixWord ++ tailWord_4299557).sum := by decide
  have hdescent : baseEnd_4299557 < baseStart_4299557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299647 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 8]
def baseStart_4299647 : Nat := 118140960795 + 4299647 * 2 ^ 59
def prefixEnd_4299647 : Nat := 4983230072969 + 3 ^ 40 * 4299647 * 2
def baseEnd_4299647 : Nat := 245309506184693816115421

theorem tailTrace_4299647 : CollatzResearch.WordTrace tailWord_4299647 prefixEnd_4299647 245309506184693816115421 := by
  unfold tailWord_4299647
  simp only [CollatzResearch.WordTrace]
  refine ⟨156821009454120715090409195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104547339636080476726939463 156821009454120715090409195)
  ·
    refine ⟨235231514181181072635613793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156821009454120715090409195 235231514181181072635613793)
    ·
      refine ⟨176423635635885804476710345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235231514181181072635613793 176423635635885804476710345)
      ·
        refine ⟨132317726726914353357532759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176423635635885804476710345 132317726726914353357532759)
        ·
          refine ⟨198476590090371530036299139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132317726726914353357532759 198476590090371530036299139)
          ·
            refine ⟨297714885135557295054448709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198476590090371530036299139 297714885135557295054448709)
            ·
              refine ⟨55821540962916992822709133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297714885135557295054448709 55821540962916992822709133)
              ·
                refine ⟨20933077861093872308515925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55821540962916992822709133 20933077861093872308515925)
                ·
                  refine ⟨245309506184693816115421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20933077861093872308515925 245309506184693816115421)
                  ·
                    rfl

theorem cell23_4299647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 8].length) (baseStart_4299647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299647 prefixEnd_4299647 := by exact prefixLift 4299647
  have htrace : WordTrace (prefixWord ++ tailWord_4299647) baseStart_4299647 baseEnd_4299647 := by
    simpa [prefixWord, tailWord_4299647, baseEnd_4299647] using wordTrace_append hprefix tailTrace_4299647
  have hstable : (prefixWord ++ tailWord_4299647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299647).length < 2 ^ (prefixWord ++ tailWord_4299647).sum := by decide
  have hdescent : baseEnd_4299647 < baseStart_4299647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299658 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4299658 : Nat := 118140960795 + 4299658 * 2 ^ 59
def prefixEnd_4299658 : Nat := 4983230072969 + 3 ^ 40 * 4299658 * 2
def baseEnd_4299658 : Nat := 2207791203949443802001239

theorem tailTrace_4299658 : CollatzResearch.WordTrace tailWord_4299658 prefixEnd_4299658 2207791203949443802001239 := by
  unfold tailWord_4299658
  simp only [CollatzResearch.WordTrace]
  refine ⟨39205352664270215992264907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104547607104720575979373085 39205352664270215992264907)
  ·
    refine ⟨58808028996405323988397361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39205352664270215992264907 58808028996405323988397361)
    ·
      refine ⟨44106021747303992991298021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58808028996405323988397361 44106021747303992991298021)
      ·
        refine ⟨8269879077619498685868379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44106021747303992991298021 8269879077619498685868379)
        ·
          refine ⟨12404818616429248028802569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8269879077619498685868379 12404818616429248028802569)
          ·
            refine ⟨9303613962321936021601927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12404818616429248028802569 9303613962321936021601927)
            ·
              refine ⟨13955420943482904032402891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9303613962321936021601927 13955420943482904032402891)
              ·
                refine ⟨20933131415224356048604337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13955420943482904032402891 20933131415224356048604337)
                ·
                  refine ⟨15699848561418267036453253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20933131415224356048604337 15699848561418267036453253)
                  ·
                    refine ⟨2943721605265925069334985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15699848561418267036453253 2943721605265925069334985)
                    ·
                      refine ⟨2207791203949443802001239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2943721605265925069334985 2207791203949443802001239)
                      ·
                        rfl

theorem cell23_4299658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4299658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299658 prefixEnd_4299658 := by exact prefixLift 4299658
  have htrace : WordTrace (prefixWord ++ tailWord_4299658) baseStart_4299658 baseEnd_4299658 := by
    simpa [prefixWord, tailWord_4299658, baseEnd_4299658] using wordTrace_append hprefix tailTrace_4299658
  have hstable : (prefixWord ++ tailWord_4299658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299658).length < 2 ^ (prefixWord ++ tailWord_4299658).sum := by decide
  have hdescent : baseEnd_4299658 < baseStart_4299658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299667 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_4299667 : Nat := 118140960795 + 4299667 * 2 ^ 59
def prefixEnd_4299667 : Nat := 4983230072969 + 3 ^ 40 * 4299667 * 2
def baseEnd_4299667 : Nat := 2207795825275334266788697

theorem tailTrace_4299667 : CollatzResearch.WordTrace tailWord_4299667 prefixEnd_4299667 2207795825275334266788697 := by
  unfold tailWord_4299667
  simp only [CollatzResearch.WordTrace]
  refine ⟨156821738914048258506137255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104547825942698839004091503 156821738914048258506137255)
  ·
    refine ⟨235232608371072387759205883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156821738914048258506137255 235232608371072387759205883)
    ·
      refine ⟨352848912556608581638808825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235232608371072387759205883 352848912556608581638808825)
      ·
        refine ⟨264636684417456436229106619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352848912556608581638808825 264636684417456436229106619)
        ·
          refine ⟨396955026626184654343659929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264636684417456436229106619 396955026626184654343659929)
          ·
            refine ⟨297716269969638490757744947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396955026626184654343659929 297716269969638490757744947)
            ·
              refine ⟨446574404954457736136617421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297716269969638490757744947 446574404954457736136617421)
              ·
                refine ⟨167465401857921651051231533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446574404954457736136617421 167465401857921651051231533)
                ·
                  refine ⟨62799525696720619144211825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167465401857921651051231533 62799525696720619144211825)
                  ·
                    refine ⟨47099644272540464358158869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62799525696720619144211825 47099644272540464358158869)
                    ·
                      refine ⟨2207795825275334266788697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47099644272540464358158869 2207795825275334266788697)
                      ·
                        rfl

theorem cell23_4299667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_4299667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299667 prefixEnd_4299667 := by exact prefixLift 4299667
  have htrace : WordTrace (prefixWord ++ tailWord_4299667) baseStart_4299667 baseEnd_4299667 := by
    simpa [prefixWord, tailWord_4299667, baseEnd_4299667] using wordTrace_append hprefix tailTrace_4299667
  have hstable : (prefixWord ++ tailWord_4299667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299667).length < 2 ^ (prefixWord ++ tailWord_4299667).sum := by decide
  have hdescent : baseEnd_4299667 < baseStart_4299667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299751 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4299751 : Nat := 118140960795 + 4299751 * 2 ^ 59
def prefixEnd_4299751 : Nat := 4983230072969 + 3 ^ 40 * 4299751 * 2
def baseEnd_4299751 : Nat := 2207838957650311938138311

theorem tailTrace_4299751 : CollatzResearch.WordTrace tailWord_4299751 prefixEnd_4299751 2207838957650311938138311 := by
  unfold tailWord_4299751
  simp only [CollatzResearch.WordTrace]
  refine ⟨156824802645743940852195107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104549868430495960568130071 156824802645743940852195107)
  ·
    refine ⟨235237203968615911278292661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156824802645743940852195107 235237203968615911278292661)
    ·
      refine ⟨22053487872057741682339937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235237203968615911278292661 22053487872057741682339937)
      ·
        refine ⟨16540115904043306261754953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22053487872057741682339937 16540115904043306261754953)
        ·
          refine ⟨12405086928032479696316215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16540115904043306261754953 12405086928032479696316215)
          ·
            refine ⟨18607630392048719544474323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12405086928032479696316215 18607630392048719544474323)
            ·
              refine ⟨27911445588073079316711485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18607630392048719544474323 27911445588073079316711485)
              ·
                refine ⟨10466792095527404743766807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27911445588073079316711485 10466792095527404743766807)
                ·
                  refine ⟨15700188143291107115650211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10466792095527404743766807 15700188143291107115650211)
                  ·
                    refine ⟨23550282214936660673475317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15700188143291107115650211 23550282214936660673475317)
                    ·
                      refine ⟨2207838957650311938138311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23550282214936660673475317 2207838957650311938138311)
                      ·
                        rfl

theorem cell23_4299751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4299751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299751 prefixEnd_4299751 := by exact prefixLift 4299751
  have htrace : WordTrace (prefixWord ++ tailWord_4299751) baseStart_4299751 baseEnd_4299751 := by
    simpa [prefixWord, tailWord_4299751, baseEnd_4299751] using wordTrace_append hprefix tailTrace_4299751
  have hstable : (prefixWord ++ tailWord_4299751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299751).length < 2 ^ (prefixWord ++ tailWord_4299751).sum := by decide
  have hdescent : baseEnd_4299751 < baseStart_4299751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299754 : List Nat := [3, 1, 3, 1, 2, 2, 11]
def baseStart_4299754 : Nat := 118140960795 + 4299754 * 2 ^ 59
def prefixEnd_4299754 : Nat := 4983230072969 + 3 ^ 40 * 4299754 * 2
def baseEnd_4299754 : Nat := 27257290099904634893837

theorem tailTrace_4299754 : CollatzResearch.WordTrace tailWord_4299754 prefixEnd_4299754 27257290099904634893837 := by
  unfold tailWord_4299754
  simp only [CollatzResearch.WordTrace]
  refine ⟨39206228016183268091138579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104549941376488714909702877 39206228016183268091138579)
  ·
    refine ⟨58809342024274902136707869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39206228016183268091138579 58809342024274902136707869)
    ·
      refine ⟨22053503259103088301265451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58809342024274902136707869 22053503259103088301265451)
      ·
        refine ⟨33080254888654632451898177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22053503259103088301265451 33080254888654632451898177)
        ·
          refine ⟨24810191166490974338923633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33080254888654632451898177 24810191166490974338923633)
          ·
            refine ⟨18607643374868230754192725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24810191166490974338923633 18607643374868230754192725)
            ·
              refine ⟨27257290099904634893837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18607643374868230754192725 27257290099904634893837)
              ·
                rfl

theorem cell23_4299754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 11].length) (baseStart_4299754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299754 prefixEnd_4299754 := by exact prefixLift 4299754
  have htrace : WordTrace (prefixWord ++ tailWord_4299754) baseStart_4299754 baseEnd_4299754 := by
    simpa [prefixWord, tailWord_4299754, baseEnd_4299754] using wordTrace_append hprefix tailTrace_4299754
  have hstable : (prefixWord ++ tailWord_4299754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299754).length < 2 ^ (prefixWord ++ tailWord_4299754).sum := by decide
  have hdescent : baseEnd_4299754 < baseStart_4299754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299781 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_4299781 : Nat := 118140960795 + 4299781 * 2 ^ 59
def prefixEnd_4299781 : Nat := 4983230072969 + 3 ^ 40 * 4299781 * 2
def baseEnd_4299781 : Nat := 2207854362069946820763173

theorem tailTrace_4299781 : CollatzResearch.WordTrace tailWord_4299781 prefixEnd_4299781 2207854362069946820763173 := by
  unfold tailWord_4299781
  simp only [CollatzResearch.WordTrace]
  refine ⟨156825896835635255975787197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104550597890423503983858131 156825896835635255975787197)
  ·
    refine ⟨58809711313363220990920199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156825896835635255975787197 58809711313363220990920199)
    ·
      refine ⟨88214566970044831486380299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58809711313363220990920199 88214566970044831486380299)
      ·
        refine ⟨132321850455067247229570449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88214566970044831486380299 132321850455067247229570449)
        ·
          refine ⟨99241387841300435422177837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132321850455067247229570449 99241387841300435422177837)
          ·
            refine ⟨37215520440487663283316689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99241387841300435422177837 37215520440487663283316689)
            ·
              refine ⟨27911640330365747462487517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37215520440487663283316689 27911640330365747462487517)
              ·
                refine ⟨10466865123887155298432819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27911640330365747462487517 10466865123887155298432819)
                ·
                  refine ⟨15700297685830732947649229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10466865123887155298432819 15700297685830732947649229)
                  ·
                    refine ⟨5887611632186524855368461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15700297685830732947649229 5887611632186524855368461)
                    ·
                      refine ⟨2207854362069946820763173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5887611632186524855368461 2207854362069946820763173)
                      ·
                        rfl

theorem cell23_4299781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_4299781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299781 prefixEnd_4299781 := by exact prefixLift 4299781
  have htrace : WordTrace (prefixWord ++ tailWord_4299781) baseStart_4299781 baseEnd_4299781 := by
    simpa [prefixWord, tailWord_4299781, baseEnd_4299781] using wordTrace_append hprefix tailTrace_4299781
  have hstable : (prefixWord ++ tailWord_4299781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299781).length < 2 ^ (prefixWord ++ tailWord_4299781).sum := by decide
  have hdescent : baseEnd_4299781 < baseStart_4299781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299871 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_4299871 : Nat := 118140960795 + 4299871 * 2 ^ 59
def prefixEnd_4299871 : Nat := 4983230072969 + 3 ^ 40 * 4299871 * 2
def baseEnd_4299871 : Nat := 2207900575328851468637759

theorem tailTrace_4299871 : CollatzResearch.WordTrace tailWord_4299871 prefixEnd_4299871 2207900575328851468637759 := by
  unfold tailWord_4299871
  simp only [CollatzResearch.WordTrace]
  refine ⟨156829179405309201346563467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104552786270206134231042311 156829179405309201346563467)
  ·
    refine ⟨235243769107963802019845201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156829179405309201346563467 235243769107963802019845201)
    ·
      refine ⟨176432826830972851514883901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235243769107963802019845201 176432826830972851514883901)
      ·
        refine ⟨66162310061614819318081463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176432826830972851514883901 66162310061614819318081463)
        ·
          refine ⟨99243465092422228977122195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66162310061614819318081463 99243465092422228977122195)
          ·
            refine ⟨148865197638633343465683293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99243465092422228977122195 148865197638633343465683293)
            ·
              refine ⟨55824449114487503799631235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148865197638633343465683293 55824449114487503799631235)
              ·
                refine ⟨83736673671731255699446853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55824449114487503799631235 83736673671731255699446853)
                ·
                  refine ⟨15700626313449610443646285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83736673671731255699446853 15700626313449610443646285)
                  ·
                    refine ⟨5887734867543603916367357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15700626313449610443646285 5887734867543603916367357)
                    ·
                      refine ⟨2207900575328851468637759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5887734867543603916367357 2207900575328851468637759)
                      ·
                        rfl

theorem cell23_4299871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_4299871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299871 prefixEnd_4299871 := by exact prefixLift 4299871
  have htrace : WordTrace (prefixWord ++ tailWord_4299871) baseStart_4299871 baseEnd_4299871 := by
    simpa [prefixWord, tailWord_4299871, baseEnd_4299871] using wordTrace_append hprefix tailTrace_4299871
  have hstable : (prefixWord ++ tailWord_4299871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299871).length < 2 ^ (prefixWord ++ tailWord_4299871).sum := by decide
  have hdescent : baseEnd_4299871 < baseStart_4299871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299912 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 5]
def baseStart_4299912 : Nat := 118140960795 + 4299912 * 2 ^ 59
def prefixEnd_4299912 : Nat := 4983230072969 + 3 ^ 40 * 4299912 * 2
def baseEnd_4299912 : Nat := 245324625337298423136119

theorem tailTrace_4299912 : CollatzResearch.WordTrace tailWord_4299912 prefixEnd_4299912 245324625337298423136119 := by
  unfold tailWord_4299912
  simp only [CollatzResearch.WordTrace]
  refine ⟨78415337399080332674402995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104553783198773776899203993 78415337399080332674402995)
  ·
    refine ⟨117623006098620499011604493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78415337399080332674402995 117623006098620499011604493)
    ·
      refine ⟨44108627286982687129351685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117623006098620499011604493 44108627286982687129351685)
      ·
        refine ⟨8270367616309253836753441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44108627286982687129351685 8270367616309253836753441)
        ·
          refine ⟨6202775712231940377565081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8270367616309253836753441 6202775712231940377565081)
          ·
            refine ⟨4652081784173955283173811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6202775712231940377565081 4652081784173955283173811)
            ·
              refine ⟨6978122676260932924760717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652081784173955283173811 6978122676260932924760717)
              ·
                refine ⟨2616796003597849846785269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6978122676260932924760717 2616796003597849846785269)
                ·
                  refine ⟨245324625337298423136119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2616796003597849846785269 245324625337298423136119)
                  ·
                    rfl

theorem cell23_4299912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 5].length) (baseStart_4299912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299912 prefixEnd_4299912 := by exact prefixLift 4299912
  have htrace : WordTrace (prefixWord ++ tailWord_4299912) baseStart_4299912 baseEnd_4299912 := by
    simpa [prefixWord, tailWord_4299912, baseEnd_4299912] using wordTrace_append hprefix tailTrace_4299912
  have hstable : (prefixWord ++ tailWord_4299912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299912).length < 2 ^ (prefixWord ++ tailWord_4299912).sum := by decide
  have hdescent : baseEnd_4299912 < baseStart_4299912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299928 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4299928 : Nat := 118140960795 + 4299928 * 2 ^ 59
def prefixEnd_4299928 : Nat := 4983230072969 + 3 ^ 40 * 4299928 * 2
def baseEnd_4299928 : Nat := 2207929843726157745624997

theorem tailTrace_4299928 : CollatzResearch.WordTrace tailWord_4299928 prefixEnd_4299928 2207929843726157745624997 := by
  unfold tailWord_4299928
  simp only [CollatzResearch.WordTrace]
  refine ⟨78415629183051350040694219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104554172244068466720925625 78415629183051350040694219)
  ·
    refine ⟨117623443774577025061041329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78415629183051350040694219 117623443774577025061041329)
    ·
      refine ⟨88217582830932768795780997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117623443774577025061041329 88217582830932768795780997)
      ·
        refine ⟨16540796780799894149208937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88217582830932768795780997 16540796780799894149208937)
        ·
          refine ⟨12405597585599920611906703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16540796780799894149208937 12405597585599920611906703)
          ·
            refine ⟨18608396378399880917860055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12405597585599920611906703 18608396378399880917860055)
            ·
              refine ⟨27912594567599821376790083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18608396378399880917860055 27912594567599821376790083)
              ·
                refine ⟨41868891851399732065185125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27912594567599821376790083 41868891851399732065185125)
                ·
                  refine ⟨7850417222137449762222211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41868891851399732065185125 7850417222137449762222211)
                  ·
                    refine ⟨11775625833206174643333317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7850417222137449762222211 11775625833206174643333317)
                    ·
                      refine ⟨2207929843726157745624997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11775625833206174643333317 2207929843726157745624997)
                      ·
                        rfl

theorem cell23_4299928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4299928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299928 prefixEnd_4299928 := by exact prefixLift 4299928
  have htrace : WordTrace (prefixWord ++ tailWord_4299928) baseStart_4299928 baseEnd_4299928 := by
    simpa [prefixWord, tailWord_4299928, baseEnd_4299928] using wordTrace_append hprefix tailTrace_4299928
  have hstable : (prefixWord ++ tailWord_4299928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299928).length < 2 ^ (prefixWord ++ tailWord_4299928).sum := by decide
  have hdescent : baseEnd_4299928 < baseStart_4299928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299931 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 3]
def baseStart_4299931 : Nat := 118140960795 + 4299931 * 2 ^ 59
def prefixEnd_4299931 : Nat := 4983230072969 + 3 ^ 40 * 4299931 * 2
def baseEnd_4299931 : Nat := 2207931384168121233887483

theorem tailTrace_4299931 : CollatzResearch.WordTrace tailWord_4299931 prefixEnd_4299931 2207931384168121233887483 := by
  unfold tailWord_4299931
  simp only [CollatzResearch.WordTrace]
  refine ⟨156831367785091831593747647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104554245190061221062498431 156831367785091831593747647)
  ·
    refine ⟨235247051677637747390621471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156831367785091831593747647 235247051677637747390621471)
    ·
      refine ⟨352870577516456621085932207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235247051677637747390621471 352870577516456621085932207)
      ·
        refine ⟨529305866274684931628898311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352870577516456621085932207 529305866274684931628898311)
        ·
          refine ⟨793958799412027397443347467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529305866274684931628898311 793958799412027397443347467)
          ·
            refine ⟨1190938199118041096165021201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793958799412027397443347467 1190938199118041096165021201)
            ·
              refine ⟨893203649338530822123765901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190938199118041096165021201 893203649338530822123765901)
              ·
                refine ⟨334951368501949058296412213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 893203649338530822123765901 334951368501949058296412213)
                ·
                  refine ⟨31401690797057724215288645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334951368501949058296412213 31401690797057724215288645)
                  ·
                    refine ⟨5887817024448323290366621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31401690797057724215288645 5887817024448323290366621)
                    ·
                      refine ⟨2207931384168121233887483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5887817024448323290366621 2207931384168121233887483)
                      ·
                        rfl

theorem cell23_4299931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 3].length) (baseStart_4299931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299931 prefixEnd_4299931 := by exact prefixLift 4299931
  have htrace : WordTrace (prefixWord ++ tailWord_4299931) baseStart_4299931 baseEnd_4299931 := by
    simpa [prefixWord, tailWord_4299931, baseEnd_4299931] using wordTrace_append hprefix tailTrace_4299931
  have hstable : (prefixWord ++ tailWord_4299931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299931).length < 2 ^ (prefixWord ++ tailWord_4299931).sum := by decide
  have hdescent : baseEnd_4299931 < baseStart_4299931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4299989 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_4299989 : Nat := 118140960795 + 4299989 * 2 ^ 59
def prefixEnd_4299989 : Nat := 4983230072969 + 3 ^ 40 * 4299989 * 2
def baseEnd_4299989 : Nat := 735987055348694002320739

theorem tailTrace_4299989 : CollatzResearch.WordTrace tailWord_4299989 prefixEnd_4299989 735987055348694002320739 := by
  unfold tailWord_4299989
  simp only [CollatzResearch.WordTrace]
  refine ⟨156833483218881707499359021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104555655479254471666239347 156833483218881707499359021)
  ·
    refine ⟨58812556207080640312259633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156833483218881707499359021 58812556207080640312259633)
    ·
      refine ⟨44109417155310480234194725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58812556207080640312259633 44109417155310480234194725)
      ·
        refine ⟨8270515716620715043911511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44109417155310480234194725 8270515716620715043911511)
        ·
          refine ⟨12405773574931072565867267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8270515716620715043911511 12405773574931072565867267)
          ·
            refine ⟨18608660362396608848800901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12405773574931072565867267 18608660362396608848800901)
            ·
              refine ⟨3489123817949364159150169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18608660362396608848800901 3489123817949364159150169)
              ·
                refine ⟨2616842863462023119362627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3489123817949364159150169 2616842863462023119362627)
                ·
                  refine ⟨3925264295193034679043941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616842863462023119362627 3925264295193034679043941)
                  ·
                    refine ⟨735987055348694002320739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925264295193034679043941 735987055348694002320739)
                    ·
                      rfl

theorem cell23_4299989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_4299989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4299989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4299989 prefixEnd_4299989 := by exact prefixLift 4299989
  have htrace : WordTrace (prefixWord ++ tailWord_4299989) baseStart_4299989 baseEnd_4299989 := by
    simpa [prefixWord, tailWord_4299989, baseEnd_4299989] using wordTrace_append hprefix tailTrace_4299989
  have hstable : (prefixWord ++ tailWord_4299989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4299989).length < 2 ^ (prefixWord ++ tailWord_4299989).sum := by decide
  have hdescent : baseEnd_4299989 < baseStart_4299989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4299989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300035 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 4]
def baseStart_4300035 : Nat := 118140960795 + 4300035 * 2 ^ 59
def prefixEnd_4300035 : Nat := 4983230072969 + 3 ^ 40 * 4300035 * 2
def baseEnd_4300035 : Nat := 2207984786156188826987005

theorem tailTrace_4300035 : CollatzResearch.WordTrace tailWord_4300035 prefixEnd_4300035 2207984786156188826987005 := by
  unfold tailWord_4300035
  simp only [CollatzResearch.WordTrace]
  refine ⟨156835160976715057355533559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104556773984476704903689039 156835160976715057355533559)
  ·
    refine ⟨235252741465072586033300339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156835160976715057355533559 235252741465072586033300339)
    ·
      refine ⟨352879112197608879049950509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235252741465072586033300339 352879112197608879049950509)
      ·
        refine ⟨132329667074103329643731441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352879112197608879049950509 132329667074103329643731441)
        ·
          refine ⟨99247250305577497232798581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132329667074103329643731441 99247250305577497232798581)
          ·
            refine ⟨9304429716147890365574867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99247250305577497232798581 9304429716147890365574867)
            ·
              refine ⟨13956644574221835548362301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9304429716147890365574867 13956644574221835548362301)
              ·
                refine ⟨5233741715333188330635863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13956644574221835548362301 5233741715333188330635863)
                ·
                  refine ⟨7850612572999782495953795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5233741715333188330635863 7850612572999782495953795)
                  ·
                    refine ⟨11775918859499673743930693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7850612572999782495953795 11775918859499673743930693)
                    ·
                      refine ⟨2207984786156188826987005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11775918859499673743930693 2207984786156188826987005)
                      ·
                        rfl

theorem cell23_4300035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_4300035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300035 prefixEnd_4300035 := by exact prefixLift 4300035
  have htrace : WordTrace (prefixWord ++ tailWord_4300035) baseStart_4300035 baseEnd_4300035 := by
    simpa [prefixWord, tailWord_4300035, baseEnd_4300035] using wordTrace_append hprefix tailTrace_4300035
  have hstable : (prefixWord ++ tailWord_4300035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300035).length < 2 ^ (prefixWord ++ tailWord_4300035).sum := by decide
  have hdescent : baseEnd_4300035 < baseStart_4300035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300041 : List Nat := [1, 2, 1, 1, 3, 3, 12]
def baseStart_4300041 : Nat := 118140960795 + 4300041 * 2 ^ 59
def prefixEnd_4300041 : Nat := 4983230072969 + 3 ^ 40 * 4300041 * 2
def baseEnd_4300041 : Nat := 27259109469631059302617

theorem tailTrace_4300041 : CollatzResearch.WordTrace tailWord_4300041 prefixEnd_4300041 27259109469631059302617 := by
  unfold tailWord_4300041
  simp only [CollatzResearch.WordTrace]
  refine ⟨156835379814693320380251977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104556919876462213586834651 156835379814693320380251977)
  ·
    refine ⟨117626534861019990285188983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156835379814693320380251977 117626534861019990285188983)
    ·
      refine ⟨176439802291529985427783475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117626534861019990285188983 176439802291529985427783475)
      ·
        refine ⟨264659703437294978141675213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176439802291529985427783475 264659703437294978141675213)
        ·
          refine ⟨99247388788985616803128205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264659703437294978141675213 99247388788985616803128205)
          ·
            refine ⟨37217770795869606301173077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99247388788985616803128205 37217770795869606301173077)
            ·
              refine ⟨27259109469631059302617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37217770795869606301173077 27259109469631059302617)
              ·
                rfl

theorem cell23_4300041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 12].length) (baseStart_4300041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300041 prefixEnd_4300041 := by exact prefixLift 4300041
  have htrace : WordTrace (prefixWord ++ tailWord_4300041) baseStart_4300041 baseEnd_4300041 := by
    simpa [prefixWord, tailWord_4300041, baseEnd_4300041] using wordTrace_append hprefix tailTrace_4300041
  have hstable : (prefixWord ++ tailWord_4300041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300041).length < 2 ^ (prefixWord ++ tailWord_4300041).sum := by decide
  have hdescent : baseEnd_4300041 < baseStart_4300041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300051 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_4300051 : Nat := 118140960795 + 4300051 * 2 ^ 59
def prefixEnd_4300051 : Nat := 4983230072969 + 3 ^ 40 * 4300051 * 2
def baseEnd_4300051 : Nat := 2207993001846660764386931

theorem tailTrace_4300051 : CollatzResearch.WordTrace tailWord_4300051 prefixEnd_4300051 2207993001846660764386931 := by
  unfold tailWord_4300051
  simp only [CollatzResearch.WordTrace]
  refine ⟨156835744544657092088116007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104557163029771394725410671 156835744544657092088116007)
  ·
    refine ⟨235253616816985638132174011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156835744544657092088116007 235253616816985638132174011)
    ·
      refine ⟨352880425225478457198261017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235253616816985638132174011 352880425225478457198261017)
      ·
        refine ⟨264660318919108842898695763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352880425225478457198261017 264660318919108842898695763)
        ·
          refine ⟨396990478378663264348043645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264660318919108842898695763 396990478378663264348043645)
          ·
            refine ⟨148871429391998724130516367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396990478378663264348043645 148871429391998724130516367)
            ·
              refine ⟨223307144087998086195774551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148871429391998724130516367 223307144087998086195774551)
              ·
                refine ⟨334960716131997129293661827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223307144087998086195774551 334960716131997129293661827)
                ·
                  refine ⟨502441074197995693940492741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334960716131997129293661827 502441074197995693940492741)
                  ·
                    refine ⟨94207701412124192613842389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 502441074197995693940492741 94207701412124192613842389)
                    ·
                      refine ⟨2207993001846660764386931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94207701412124192613842389 2207993001846660764386931)
                      ·
                        rfl

theorem cell23_4300051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_4300051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300051 prefixEnd_4300051 := by exact prefixLift 4300051
  have htrace : WordTrace (prefixWord ++ tailWord_4300051) baseStart_4300051 baseEnd_4300051 := by
    simpa [prefixWord, tailWord_4300051, baseEnd_4300051] using wordTrace_append hprefix tailTrace_4300051
  have hstable : (prefixWord ++ tailWord_4300051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300051).length < 2 ^ (prefixWord ++ tailWord_4300051).sum := by decide
  have hdescent : baseEnd_4300051 < baseStart_4300051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300072 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_4300072 : Nat := 118140960795 + 4300072 * 2 ^ 59
def prefixEnd_4300072 : Nat := 4983230072969 + 3 ^ 40 * 4300072 * 2
def baseEnd_4300072 : Nat := 2208003784940405182224335

theorem tailTrace_4300072 : CollatzResearch.WordTrace tailWord_4300072 prefixEnd_4300072 2208003784940405182224335 := by
  unfold tailWord_4300072
  simp only [CollatzResearch.WordTrace]
  refine ⟨78418255238790506337315235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104557673651720675116420313 78418255238790506337315235)
  ·
    refine ⟨117627382858185759505972853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78418255238790506337315235 117627382858185759505972853)
    ·
      refine ⟨11027567142954914953684955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117627382858185759505972853 11027567142954914953684955)
      ·
        refine ⟨16541350714432372430527433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11027567142954914953684955 16541350714432372430527433)
        ·
          refine ⟨12406013035824279322895575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16541350714432372430527433 12406013035824279322895575)
          ·
            refine ⟨18609019553736418984343363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12406013035824279322895575 18609019553736418984343363)
            ·
              refine ⟨27913529330604628476515045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18609019553736418984343363 27913529330604628476515045)
              ·
                refine ⟨5233786749488367839346571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27913529330604628476515045 5233786749488367839346571)
                ·
                  refine ⟨7850680124232551759019857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5233786749488367839346571 7850680124232551759019857)
                  ·
                    refine ⟨5888010093174413819264893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7850680124232551759019857 5888010093174413819264893)
                    ·
                      refine ⟨2208003784940405182224335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888010093174413819264893 2208003784940405182224335)
                      ·
                        rfl

theorem cell23_4300072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_4300072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300072 prefixEnd_4300072 := by exact prefixLift 4300072
  have htrace : WordTrace (prefixWord ++ tailWord_4300072) baseStart_4300072 baseEnd_4300072 := by
    simpa [prefixWord, tailWord_4300072, baseEnd_4300072] using wordTrace_append hprefix tailTrace_4300072
  have hstable : (prefixWord ++ tailWord_4300072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300072).length < 2 ^ (prefixWord ++ tailWord_4300072).sum := by decide
  have hdescent : baseEnd_4300072 < baseStart_4300072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300119 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 2, 1, 3]
def baseStart_4300119 : Nat := 118140960795 + 4300119 * 2 ^ 59
def prefixEnd_4300119 : Nat := 4983230072969 + 3 ^ 40 * 4300119 * 2
def baseEnd_4300119 : Nat := 2208027918531166498336619

theorem tailTrace_4300119 : CollatzResearch.WordTrace tailWord_4300119 prefixEnd_4300119 2208027918531166498336619 := by
  unfold tailWord_4300119
  simp only [CollatzResearch.WordTrace]
  refine ⟨156838224708410739701591411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104558816472273826467727607 156838224708410739701591411)
  ·
    refine ⟨235257337062616109552387117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156838224708410739701591411 235257337062616109552387117)
    ·
      refine ⟨88221501398481041082145169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235257337062616109552387117 88221501398481041082145169)
      ·
        refine ⟨66166126048860780811608877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88221501398481041082145169 66166126048860780811608877)
        ·
          refine ⟨24812297268322792804353329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66166126048860780811608877 24812297268322792804353329)
          ·
            refine ⟨18609222951242094603264997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24812297268322792804353329 18609222951242094603264997)
            ·
              refine ⟨3489229303357892738112187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18609222951242094603264997 3489229303357892738112187)
              ·
                refine ⟨5233843955036839107168281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489229303357892738112187 5233843955036839107168281)
                ·
                  refine ⟨3925382966277629330376211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5233843955036839107168281 3925382966277629330376211)
                  ·
                    refine ⟨5888074449416443995564317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3925382966277629330376211 5888074449416443995564317)
                    ·
                      refine ⟨2208027918531166498336619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888074449416443995564317 2208027918531166498336619)
                      ·
                        rfl

theorem cell23_4300119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_4300119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300119 prefixEnd_4300119 := by exact prefixLift 4300119
  have htrace : WordTrace (prefixWord ++ tailWord_4300119) baseStart_4300119 baseEnd_4300119 := by
    simpa [prefixWord, tailWord_4300119, baseEnd_4300119] using wordTrace_append hprefix tailTrace_4300119
  have hstable : (prefixWord ++ tailWord_4300119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300119).length < 2 ^ (prefixWord ++ tailWord_4300119).sum := by decide
  have hdescent : baseEnd_4300119 < baseStart_4300119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300215 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_4300215 : Nat := 118140960795 + 4300215 * 2 ^ 59
def prefixEnd_4300215 : Nat := 4983230072969 + 3 ^ 40 * 4300215 * 2
def baseEnd_4300215 : Nat := 2208077212673998122736177

theorem tailTrace_4300215 : CollatzResearch.WordTrace tailWord_4300215 prefixEnd_4300215 2208077212673998122736177 := by
  unfold tailWord_4300215
  simp only [CollatzResearch.WordTrace]
  refine ⟨156841726116062948097086099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104561150744041965398057399 156841726116062948097086099)
  ·
    refine ⟨235262589174094422145629149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156841726116062948097086099 235262589174094422145629149)
    ·
      refine ⟨88223470940285408304610931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235262589174094422145629149 88223470940285408304610931)
      ·
        refine ⟨132335206410428112456916397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88223470940285408304610931 132335206410428112456916397)
        ·
          refine ⟨49625702403910542171343649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132335206410428112456916397 49625702403910542171343649)
          ·
            refine ⟨37219276802932906628507737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49625702403910542171343649 37219276802932906628507737)
            ·
              refine ⟨27914457602199679971380803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37219276802932906628507737 27914457602199679971380803)
              ·
                refine ⟨41871686403299519957071205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27914457602199679971380803 41871686403299519957071205)
                ·
                  refine ⟨7850941200618659991950851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41871686403299519957071205 7850941200618659991950851)
                  ·
                    refine ⟨11776411800927989987926277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7850941200618659991950851 11776411800927989987926277)
                    ·
                      refine ⟨2208077212673998122736177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11776411800927989987926277 2208077212673998122736177)
                      ·
                        rfl

theorem cell23_4300215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_4300215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300215 prefixEnd_4300215 := by exact prefixLift 4300215
  have htrace : WordTrace (prefixWord ++ tailWord_4300215) baseStart_4300215 baseEnd_4300215 := by
    simpa [prefixWord, tailWord_4300215, baseEnd_4300215] using wordTrace_append hprefix tailTrace_4300215
  have hstable : (prefixWord ++ tailWord_4300215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300215).length < 2 ^ (prefixWord ++ tailWord_4300215).sum := by decide
  have hdescent : baseEnd_4300215 < baseStart_4300215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300232 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_4300232 : Nat := 118140960795 + 4300232 * 2 ^ 59
def prefixEnd_4300232 : Nat := 4983230072969 + 3 ^ 40 * 4300232 * 2
def baseEnd_4300232 : Nat := 2208085941845124556223599

theorem tailTrace_4300232 : CollatzResearch.WordTrace tailWord_4300232 prefixEnd_4300232 2208085941845124556223599 := by
  unfold tailWord_4300232
  simp only [CollatzResearch.WordTrace]
  refine ⟨78421173078500680000227475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104561564104667573333636633 78421173078500680000227475)
  ·
    refine ⟨117631759617751020000341213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78421173078500680000227475 117631759617751020000341213)
    ·
      refine ⟨44111909856656632500127955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117631759617751020000341213 44111909856656632500127955)
      ·
        refine ⟨66167864784984948750191933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44111909856656632500127955 66167864784984948750191933)
        ·
          refine ⟨24812949294369355781321975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66167864784984948750191933 24812949294369355781321975)
          ·
            refine ⟨37219423941554033671982963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24812949294369355781321975 37219423941554033671982963)
            ·
              refine ⟨55829135912331050507974445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37219423941554033671982963 55829135912331050507974445)
              ·
                refine ⟨20935925967124143940490417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55829135912331050507974445 20935925967124143940490417)
                ·
                  refine ⟨15701944475343107955367813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20935925967124143940490417 15701944475343107955367813)
                  ·
                    refine ⟨2944114589126832741631465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15701944475343107955367813 2944114589126832741631465)
                    ·
                      refine ⟨2208085941845124556223599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944114589126832741631465 2208085941845124556223599)
                      ·
                        rfl

theorem cell23_4300232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_4300232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300232 prefixEnd_4300232 := by exact prefixLift 4300232
  have htrace : WordTrace (prefixWord ++ tailWord_4300232) baseStart_4300232 baseEnd_4300232 := by
    simpa [prefixWord, tailWord_4300232, baseEnd_4300232] using wordTrace_append hprefix tailTrace_4300232
  have hstable : (prefixWord ++ tailWord_4300232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300232).length < 2 ^ (prefixWord ++ tailWord_4300232).sum := by decide
  have hdescent : baseEnd_4300232 < baseStart_4300232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300235 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 3]
def baseStart_4300235 : Nat := 118140960795 + 4300235 * 2 ^ 59
def prefixEnd_4300235 : Nat := 4983230072969 + 3 ^ 40 * 4300235 * 2
def baseEnd_4300235 : Nat := 2208087482287088044486085

theorem tailTrace_4300235 : CollatzResearch.WordTrace tailWord_4300235 prefixEnd_4300235 2208087482287088044486085 := by
  unfold tailWord_4300235
  simp only [CollatzResearch.WordTrace]
  refine ⟨156842455575990491512814159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104561637050660327675209439 156842455575990491512814159)
  ·
    refine ⟨235263683363985737269221239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156842455575990491512814159 235263683363985737269221239)
    ·
      refine ⟨352895525045978605903831859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235263683363985737269221239 352895525045978605903831859)
      ·
        refine ⟨529343287568967908855747789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352895525045978605903831859 529343287568967908855747789)
        ·
          refine ⟨198503732838362965820905421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 529343287568967908855747789 198503732838362965820905421)
          ·
            refine ⟨74438899814386112182839533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198503732838362965820905421 74438899814386112182839533)
            ·
              refine ⟨27914587430394792068564825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74438899814386112182839533 27914587430394792068564825)
              ·
                refine ⟨20935940572796094051423619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27914587430394792068564825 20935940572796094051423619)
                ·
                  refine ⟨31403910859194141077135429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20935940572796094051423619 31403910859194141077135429)
                  ·
                    refine ⟨5888233286098901451962893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31403910859194141077135429 5888233286098901451962893)
                    ·
                      refine ⟨2208087482287088044486085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888233286098901451962893 2208087482287088044486085)
                      ·
                        rfl

theorem cell23_4300235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 3].length) (baseStart_4300235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300235 prefixEnd_4300235 := by exact prefixLift 4300235
  have htrace : WordTrace (prefixWord ++ tailWord_4300235) baseStart_4300235 baseEnd_4300235 := by
    simpa [prefixWord, tailWord_4300235, baseEnd_4300235] using wordTrace_append hprefix tailTrace_4300235
  have hstable : (prefixWord ++ tailWord_4300235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300235).length < 2 ^ (prefixWord ++ tailWord_4300235).sum := by decide
  have hdescent : baseEnd_4300235 < baseStart_4300235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300245 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4300245 : Nat := 118140960795 + 4300245 * 2 ^ 59
def prefixEnd_4300245 : Nat := 4983230072969 + 3 ^ 40 * 4300245 * 2
def baseEnd_4300245 : Nat := 2208092617093633005361039

theorem tailTrace_4300245 : CollatzResearch.WordTrace tailWord_4300245 prefixEnd_4300245 2208092617093633005361039 := by
  unfold tailWord_4300245
  simp only [CollatzResearch.WordTrace]
  refine ⟨156842820305954263220678189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104561880203969508813785459 156842820305954263220678189)
  ·
    refine ⟨58816057614732848707754321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156842820305954263220678189 58816057614732848707754321)
    ·
      refine ⟨44112043211049636530815741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58816057614732848707754321 44112043211049636530815741)
      ·
        refine ⟨16542016204143613699055903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44112043211049636530815741 16542016204143613699055903)
        ·
          refine ⟨24813024306215420548583855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16542016204143613699055903 24813024306215420548583855)
          ·
            refine ⟨37219536459323130822875783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24813024306215420548583855 37219536459323130822875783)
            ·
              refine ⟨55829304688984696234313675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37219536459323130822875783 55829304688984696234313675)
              ·
                refine ⟨83743957033477044351470513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55829304688984696234313675 83743957033477044351470513)
                ·
                  refine ⟨62807967775107783263602885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83743957033477044351470513 62807967775107783263602885)
                  ·
                    refine ⟨11776493957832709361925541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62807967775107783263602885 11776493957832709361925541)
                    ·
                      refine ⟨2208092617093633005361039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11776493957832709361925541 2208092617093633005361039)
                      ·
                        rfl

theorem cell23_4300245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4300245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300245 prefixEnd_4300245 := by exact prefixLift 4300245
  have htrace : WordTrace (prefixWord ++ tailWord_4300245) baseStart_4300245 baseEnd_4300245 := by
    simpa [prefixWord, tailWord_4300245, baseEnd_4300245] using wordTrace_append hprefix tailTrace_4300245
  have hstable : (prefixWord ++ tailWord_4300245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300245).length < 2 ^ (prefixWord ++ tailWord_4300245).sum := by decide
  have hdescent : baseEnd_4300245 < baseStart_4300245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300309 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_4300309 : Nat := 118140960795 + 4300309 * 2 ^ 59
def prefixEnd_4300309 : Nat := 4983230072969 + 3 ^ 40 * 4300309 * 2
def baseEnd_4300309 : Nat := 2208125479855520754960745

theorem tailTrace_4300309 : CollatzResearch.WordTrace tailWord_4300309 prefixEnd_4300309 2208125479855520754960745 := by
  unfold tailWord_4300309
  simp only [CollatzResearch.WordTrace]
  refine ⟨156845154577722402151007981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104563436385148268100671987 156845154577722402151007981)
  ·
    refine ⟨58816932966645900806627993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156845154577722402151007981 58816932966645900806627993)
    ·
      refine ⟨44112699724984425604970995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58816932966645900806627993 44112699724984425604970995)
      ·
        refine ⟨66169049587476638407456493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44112699724984425604970995 66169049587476638407456493)
        ·
          refine ⟨24813393595303739402796185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66169049587476638407456493 24813393595303739402796185)
          ·
            refine ⟨18610045196477804552097139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24813393595303739402796185 18610045196477804552097139)
            ·
              refine ⟨27915067794716706828145709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18610045196477804552097139 27915067794716706828145709)
              ·
                refine ⟨10468150423018765060554641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27915067794716706828145709 10468150423018765060554641)
                ·
                  refine ⟨7851112817264073795415981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10468150423018765060554641 7851112817264073795415981)
                  ·
                    refine ⟨2944167306474027673280993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7851112817264073795415981 2944167306474027673280993)
                    ·
                      refine ⟨2208125479855520754960745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944167306474027673280993 2208125479855520754960745)
                      ·
                        rfl

theorem cell23_4300309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_4300309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300309 prefixEnd_4300309 := by exact prefixLift 4300309
  have htrace : WordTrace (prefixWord ++ tailWord_4300309) baseStart_4300309 baseEnd_4300309 := by
    simpa [prefixWord, tailWord_4300309, baseEnd_4300309] using wordTrace_append hprefix tailTrace_4300309
  have hstable : (prefixWord ++ tailWord_4300309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300309).length < 2 ^ (prefixWord ++ tailWord_4300309).sum := by decide
  have hdescent : baseEnd_4300309 < baseStart_4300309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300316 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_4300316 : Nat := 118140960795 + 4300316 * 2 ^ 59
def prefixEnd_4300316 : Nat := 4983230072969 + 3 ^ 40 * 4300316 * 2
def baseEnd_4300316 : Nat := 2208129074220102227573213

theorem tailTrace_4300316 : CollatzResearch.WordTrace tailWord_4300316 prefixEnd_4300316 2208129074220102227573213 := by
  unfold tailWord_4300316
  simp only [CollatzResearch.WordTrace]
  refine ⟨78422704944348521173256401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104563606592464694897675201 78422704944348521173256401)
  ·
    refine ⟨58817028708261390879942301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78422704944348521173256401 58817028708261390879942301)
    ·
      refine ⟨22056385765598021579978363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58817028708261390879942301 22056385765598021579978363)
      ·
        refine ⟨33084578648397032369967545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22056385765598021579978363 33084578648397032369967545)
        ·
          refine ⟨24813433986297774277475659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33084578648397032369967545 24813433986297774277475659)
          ·
            refine ⟨37220150979446661416213489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24813433986297774277475659 37220150979446661416213489)
            ·
              refine ⟨27915113234584996062160117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37220150979446661416213489 27915113234584996062160117)
              ·
                refine ⟨2617041865742343380827511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27915113234584996062160117 2617041865742343380827511)
                ·
                  refine ⟨3925562798613515071241267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617041865742343380827511 3925562798613515071241267)
                  ·
                    refine ⟨5888344197920272606861901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3925562798613515071241267 5888344197920272606861901)
                    ·
                      refine ⟨2208129074220102227573213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888344197920272606861901 2208129074220102227573213)
                      ·
                        rfl

theorem cell23_4300316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_4300316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300316 prefixEnd_4300316 := by exact prefixLift 4300316
  have htrace : WordTrace (prefixWord ++ tailWord_4300316) baseStart_4300316 baseEnd_4300316 := by
    simpa [prefixWord, tailWord_4300316, baseEnd_4300316] using wordTrace_append hprefix tailTrace_4300316
  have hstable : (prefixWord ++ tailWord_4300316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300316).length < 2 ^ (prefixWord ++ tailWord_4300316).sum := by decide
  have hdescent : baseEnd_4300316 < baseStart_4300316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300349 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_4300349 : Nat := 118140960795 + 4300349 * 2 ^ 59
def prefixEnd_4300349 : Nat := 4983230072969 + 3 ^ 40 * 4300349 * 2
def baseEnd_4300349 : Nat := 736048673027233532820187

theorem tailTrace_4300349 : CollatzResearch.WordTrace tailWord_4300349 prefixEnd_4300349 736048673027233532820187 := by
  unfold tailWord_4300349
  simp only [CollatzResearch.WordTrace]
  refine ⟨156846613497577488982464101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104564408998384992654976067 156846613497577488982464101)
  ·
    refine ⟨29408740030795779184212019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156846613497577488982464101 29408740030795779184212019)
    ·
      refine ⟨44113110046193668776318029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29408740030795779184212019 44113110046193668776318029)
      ·
        refine ⟨16542416267322625791119261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44113110046193668776318029 16542416267322625791119261)
        ·
          refine ⟨6203406100245984671669723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16542416267322625791119261 6203406100245984671669723)
          ·
            refine ⟨9305109150368977007504585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6203406100245984671669723 9305109150368977007504585)
            ·
              refine ⟨6978831862776732755628439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9305109150368977007504585 6978831862776732755628439)
              ·
                refine ⟨10468247794165099133442659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6978831862776732755628439 10468247794165099133442659)
                ·
                  refine ⟨15702371691247648700163989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10468247794165099133442659 15702371691247648700163989)
                  ·
                    refine ⟨736048673027233532820187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15702371691247648700163989 736048673027233532820187)
                    ·
                      rfl

theorem cell23_4300349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_4300349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300349 prefixEnd_4300349 := by exact prefixLift 4300349
  have htrace : WordTrace (prefixWord ++ tailWord_4300349) baseStart_4300349 baseEnd_4300349 := by
    simpa [prefixWord, tailWord_4300349, baseEnd_4300349] using wordTrace_append hprefix tailTrace_4300349
  have hstable : (prefixWord ++ tailWord_4300349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300349).length < 2 ^ (prefixWord ++ tailWord_4300349).sum := by decide
  have hdescent : baseEnd_4300349 < baseStart_4300349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300362 : List Nat := [3, 1, 2, 1, 1, 3, 5, 7]
def baseStart_4300362 : Nat := 118140960795 + 4300362 * 2 ^ 59
def prefixEnd_4300362 : Nat := 4983230072969 + 3 ^ 40 * 4300362 * 2
def baseEnd_4300362 : Nat := 81783433123341075836963

theorem tailTrace_4300362 : CollatzResearch.WordTrace tailWord_4300362 prefixEnd_4300362 81783433123341075836963 := by
  unfold tailWord_4300362
  simp only [CollatzResearch.WordTrace]
  refine ⟨39211771911632598050671835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104564725097686928135124893 39211771911632598050671835)
  ·
    refine ⟨58817657867448897076007753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39211771911632598050671835 58817657867448897076007753)
    ·
      refine ⟨44113243400586672807005815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58817657867448897076007753 44113243400586672807005815)
      ·
        refine ⟨66169865100880009210508723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44113243400586672807005815 66169865100880009210508723)
        ·
          refine ⟨99254797651320013815763085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66169865100880009210508723 99254797651320013815763085)
          ·
            refine ⟨37220549119245005180911157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99254797651320013815763085 37220549119245005180911157)
            ·
              refine ⟨3489426479929219235710421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37220549119245005180911157 3489426479929219235710421)
              ·
                refine ⟨81783433123341075836963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3489426479929219235710421 81783433123341075836963)
                ·
                  rfl

theorem cell23_4300362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_4300362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300362 prefixEnd_4300362 := by exact prefixLift 4300362
  have htrace : WordTrace (prefixWord ++ tailWord_4300362) baseStart_4300362 baseEnd_4300362 := by
    simpa [prefixWord, tailWord_4300362, baseEnd_4300362] using wordTrace_append hprefix tailTrace_4300362
  have hstable : (prefixWord ++ tailWord_4300362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300362).length < 2 ^ (prefixWord ++ tailWord_4300362).sum := by decide
  have hdescent : baseEnd_4300362 < baseStart_4300362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300406 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4300406 : Nat := 118140960795 + 4300406 * 2 ^ 59
def prefixEnd_4300406 : Nat := 4983230072969 + 3 ^ 40 * 4300406 * 2
def baseEnd_4300406 : Nat := 2208175287479006875447799

theorem tailTrace_4300406 : CollatzResearch.WordTrace tailWord_4300406 prefixEnd_4300406 2208175287479006875447799 := by
  unfold tailWord_4300406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803043278648186732330567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104565794972247325144859381 9803043278648186732330567)
  ·
    refine ⟨14704564917972280098495851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9803043278648186732330567 14704564917972280098495851)
    ·
      refine ⟨22056847376958420147743777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14704564917972280098495851 22056847376958420147743777)
      ·
        refine ⟨16542635532718815110807833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22056847376958420147743777 16542635532718815110807833)
        ·
          refine ⟨12406976649539111333105875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16542635532718815110807833 12406976649539111333105875)
          ·
            refine ⟨18610464974308666999658813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12406976649539111333105875 18610464974308666999658813)
            ·
              refine ⟨6978924365365750124872055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18610464974308666999658813 6978924365365750124872055)
              ·
                refine ⟨10468386548048625187308083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6978924365365750124872055 10468386548048625187308083)
                ·
                  refine ⟨15702579822072937780962125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10468386548048625187308083 15702579822072937780962125)
                  ·
                    refine ⟨5888467433277351667860797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15702579822072937780962125 5888467433277351667860797)
                    ·
                      refine ⟨2208175287479006875447799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888467433277351667860797 2208175287479006875447799)
                      ·
                        rfl

theorem cell23_4300406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4300406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300406 prefixEnd_4300406 := by exact prefixLift 4300406
  have htrace : WordTrace (prefixWord ++ tailWord_4300406) baseStart_4300406 baseEnd_4300406 := by
    simpa [prefixWord, tailWord_4300406, baseEnd_4300406] using wordTrace_append hprefix tailTrace_4300406
  have hstable : (prefixWord ++ tailWord_4300406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300406).length < 2 ^ (prefixWord ++ tailWord_4300406).sum := by decide
  have hdescent : baseEnd_4300406 < baseStart_4300406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300416 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 1, 3, 2]
def baseStart_4300416 : Nat := 118140960795 + 4300416 * 2 ^ 59
def prefixEnd_4300416 : Nat := 4983230072969 + 3 ^ 40 * 4300416 * 2
def baseEnd_4300416 : Nat := 2208180422285551836322753

theorem tailTrace_4300416 : CollatzResearch.WordTrace tailWord_4300416 prefixEnd_4300416 2208180422285551836322753 := by
  unfold tailWord_4300416
  simp only [CollatzResearch.WordTrace]
  refine ⟨78424528594167379712576551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104566038125556506283435401 78424528594167379712576551)
  ·
    refine ⟨117636792891251069568864827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78424528594167379712576551 117636792891251069568864827)
    ·
      refine ⟨176455189336876604353297241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117636792891251069568864827 176455189336876604353297241)
      ·
        refine ⟨132341392002657453264972931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176455189336876604353297241 132341392002657453264972931)
        ·
          refine ⟨198512088003986179897459397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132341392002657453264972931 198512088003986179897459397)
          ·
            refine ⟨37221016500747408730773637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198512088003986179897459397 37221016500747408730773637)
            ·
              refine ⟨6978940593890139137020057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37221016500747408730773637 6978940593890139137020057)
              ·
                refine ⟨5234205445417604352765043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6978940593890139137020057 5234205445417604352765043)
                ·
                  refine ⟨7851308168126406529147565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5234205445417604352765043 7851308168126406529147565)
                  ·
                    refine ⟨2944240563047402448430337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7851308168126406529147565 2944240563047402448430337)
                    ·
                      refine ⟨2208180422285551836322753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944240563047402448430337 2208180422285551836322753)
                      ·
                        rfl

theorem cell23_4300416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_4300416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300416 prefixEnd_4300416 := by exact prefixLift 4300416
  have htrace : WordTrace (prefixWord ++ tailWord_4300416) baseStart_4300416 baseEnd_4300416 := by
    simpa [prefixWord, tailWord_4300416, baseEnd_4300416] using wordTrace_append hprefix tailTrace_4300416
  have hstable : (prefixWord ++ tailWord_4300416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300416).length < 2 ^ (prefixWord ++ tailWord_4300416).sum := by decide
  have hdescent : baseEnd_4300416 < baseStart_4300416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300424 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4300424 : Nat := 118140960795 + 4300424 * 2 ^ 59
def prefixEnd_4300424 : Nat := 4983230072969 + 3 ^ 40 * 4300424 * 2
def baseEnd_4300424 : Nat := 2208184530130787805022717

theorem tailTrace_4300424 : CollatzResearch.WordTrace tailWord_4300424 prefixEnd_4300424 2208184530130787805022717 := by
  unfold tailWord_4300424
  simp only [CollatzResearch.WordTrace]
  refine ⟨78424674486152888395722163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104566232648203851194296217 78424674486152888395722163)
  ·
    refine ⟨117637011729229332593583245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78424674486152888395722163 117637011729229332593583245)
    ·
      refine ⟨44113879398460999722593717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117637011729229332593583245 44113879398460999722593717)
      ·
        refine ⟨4135676193605718723993161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44113879398460999722593717 4135676193605718723993161)
        ·
          refine ⟨3101757145204289042994871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4135676193605718723993161 3101757145204289042994871)
          ·
            refine ⟨4652635717806433564492307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3101757145204289042994871 4652635717806433564492307)
            ·
              refine ⟨6978953576709650346738461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652635717806433564492307 6978953576709650346738461)
              ·
                refine ⟨2617107591266118880026923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6978953576709650346738461 2617107591266118880026923)
                ·
                  refine ⟨3925661386899178320040385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617107591266118880026923 3925661386899178320040385)
                  ·
                    refine ⟨2944246040174383740030289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3925661386899178320040385 2944246040174383740030289)
                    ·
                      refine ⟨2208184530130787805022717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944246040174383740030289 2208184530130787805022717)
                      ·
                        rfl

theorem cell23_4300424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4300424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300424 prefixEnd_4300424 := by exact prefixLift 4300424
  have htrace : WordTrace (prefixWord ++ tailWord_4300424) baseStart_4300424 baseEnd_4300424 := by
    simpa [prefixWord, tailWord_4300424, baseEnd_4300424] using wordTrace_append hprefix tailTrace_4300424
  have hstable : (prefixWord ++ tailWord_4300424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300424).length < 2 ^ (prefixWord ++ tailWord_4300424).sum := by decide
  have hdescent : baseEnd_4300424 < baseStart_4300424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300529 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 5, 4]
def baseStart_4300529 : Nat := 118140960795 + 4300529 * 2 ^ 59
def prefixEnd_4300529 : Nat := 4983230072969 + 3 ^ 40 * 4300529 * 2
def baseEnd_4300529 : Nat := 736079481866503298069911

theorem tailTrace_4300529 : CollatzResearch.WordTrace tailWord_4300529 prefixEnd_4300529 736079481866503298069911 := by
  unfold tailWord_4300529
  simp only [CollatzResearch.WordTrace]
  refine ⟨156853178636925379724016641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104568785757950253149344427 156853178636925379724016641)
  ·
    refine ⟨117639883977694034793012481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156853178636925379724016641 117639883977694034793012481)
    ·
      refine ⟨88229912983270526094759361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117639883977694034793012481 88229912983270526094759361)
      ·
        refine ⟨66172434737452894571069521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88229912983270526094759361 66172434737452894571069521)
        ·
          refine ⟨49629326053089670928302141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66172434737452894571069521 49629326053089670928302141)
          ·
            refine ⟨18610997269908626598113303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49629326053089670928302141 18610997269908626598113303)
            ·
              refine ⟨27916495904862939897169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18610997269908626598113303 27916495904862939897169955)
              ·
                refine ⟨41874743857294409845754933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27916495904862939897169955 41874743857294409845754933)
                ·
                  refine ⟨3925757236621350923039525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41874743857294409845754933 3925757236621350923039525)
                  ·
                    refine ⟨736079481866503298069911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925757236621350923039525 736079481866503298069911)
                    ·
                      rfl

theorem cell23_4300529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_4300529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300529 prefixEnd_4300529 := by exact prefixLift 4300529
  have htrace : WordTrace (prefixWord ++ tailWord_4300529) baseStart_4300529 baseEnd_4300529 := by
    simpa [prefixWord, tailWord_4300529, baseEnd_4300529] using wordTrace_append hprefix tailTrace_4300529
  have hstable : (prefixWord ++ tailWord_4300529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300529).length < 2 ^ (prefixWord ++ tailWord_4300529).sum := by decide
  have hdescent : baseEnd_4300529 < baseStart_4300529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300539 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 3]
def baseStart_4300539 : Nat := 118140960795 + 4300539 * 2 ^ 59
def prefixEnd_4300539 : Nat := 4983230072969 + 3 ^ 40 * 4300539 * 2
def baseEnd_4300539 : Nat := 2208243580406054855084687

theorem tailTrace_4300539 : CollatzResearch.WordTrace tailWord_4300539 prefixEnd_4300539 2208243580406054855084687 := by
  unfold tailWord_4300539
  simp only [CollatzResearch.WordTrace]
  refine ⟨156853543366889151431880671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104569028911259434287920447 156853543366889151431880671)
  ·
    refine ⟨235280315050333727147821007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156853543366889151431880671 235280315050333727147821007)
    ·
      refine ⟨352920472575500590721731511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235280315050333727147821007 352920472575500590721731511)
      ·
        refine ⟨529380708863250886082597267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352920472575500590721731511 529380708863250886082597267)
        ·
          refine ⟨794071063294876329123895901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529380708863250886082597267 794071063294876329123895901)
          ·
            refine ⟨297776648735578623421460963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 794071063294876329123895901 297776648735578623421460963)
            ·
              refine ⟨446664973103367935132191445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297776648735578623421460963 446664973103367935132191445)
              ·
                refine ⟨10468710307110185979660737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 446664973103367935132191445 10468710307110185979660737)
                ·
                  refine ⟨7851532730332639484745553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10468710307110185979660737 7851532730332639484745553)
                  ·
                    refine ⟨5888649547749479613559165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7851532730332639484745553 5888649547749479613559165)
                    ·
                      refine ⟨2208243580406054855084687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888649547749479613559165 2208243580406054855084687)
                      ·
                        rfl

theorem cell23_4300539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 3].length) (baseStart_4300539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300539 prefixEnd_4300539 := by exact prefixLift 4300539
  have htrace : WordTrace (prefixWord ++ tailWord_4300539) baseStart_4300539 baseEnd_4300539 := by
    simpa [prefixWord, tailWord_4300539, baseEnd_4300539] using wordTrace_append hprefix tailTrace_4300539
  have hstable : (prefixWord ++ tailWord_4300539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300539).length < 2 ^ (prefixWord ++ tailWord_4300539).sum := by decide
  have hdescent : baseEnd_4300539 < baseStart_4300539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
