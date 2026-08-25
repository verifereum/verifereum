Theory vfmTest0101[no_sig_docs]
Ancestors vfmTestDefs0101
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0101_0.nsv", "result0101_1.nsv", "result0101_2.nsv"];
val thyn = "vfmTestDefs0101";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
