Theory vfmTest0132[no_sig_docs]
Ancestors vfmTestDefs0132
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0132_0.nsv", "result0132_1.nsv", "result0132_2.nsv", "result0132_3.nsv"];
val thyn = "vfmTestDefs0132";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
