Theory vfmTest0019[no_sig_docs]
Ancestors vfmTestDefs0019
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0019_0.nsv", "result0019_1.nsv", "result0019_2.nsv"];
val thyn = "vfmTestDefs0019";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
