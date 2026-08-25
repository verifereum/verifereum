Theory vfmTest0358[no_sig_docs]
Ancestors vfmTestDefs0358
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0358_0.nsv", "result0358_1.nsv"];
val thyn = "vfmTestDefs0358";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
