Theory vfmTest0079[no_sig_docs]
Ancestors vfmTestDefs0079
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0079_0.nsv", "result0079_1.nsv"];
val thyn = "vfmTestDefs0079";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
