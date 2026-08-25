Theory vfmTest0084[no_sig_docs]
Ancestors vfmTestDefs0084
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0084_0.nsv", "result0084_1.nsv", "result0084_2.nsv"];
val thyn = "vfmTestDefs0084";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
