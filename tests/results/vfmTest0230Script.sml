Theory vfmTest0230[no_sig_docs]
Ancestors vfmTestDefs0230
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0230_0.nsv", "result0230_1.nsv"];
val thyn = "vfmTestDefs0230";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
