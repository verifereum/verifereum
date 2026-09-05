Theory vfmTest0255[no_sig_docs]
Ancestors vfmTestDefs0255
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0255_0.nsv", "result0255_1.nsv"];
val thyn = "vfmTestDefs0255";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
