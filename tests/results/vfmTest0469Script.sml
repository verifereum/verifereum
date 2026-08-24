Theory vfmTest0469[no_sig_docs]
Ancestors vfmTestDefs0469
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0469_0.nsv", "result0469_1.nsv", "result0469_2.nsv"];
val thyn = "vfmTestDefs0469";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
