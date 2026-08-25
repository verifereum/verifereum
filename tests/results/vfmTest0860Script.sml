Theory vfmTest0860[no_sig_docs]
Ancestors vfmTestDefs0860
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0860_0.nsv", "result0860_1.nsv"];
val thyn = "vfmTestDefs0860";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
