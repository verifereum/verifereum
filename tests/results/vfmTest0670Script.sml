Theory vfmTest0670[no_sig_docs]
Ancestors vfmTestDefs0670
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0670_0.nsv", "result0670_1.nsv", "result0670_2.nsv"];
val thyn = "vfmTestDefs0670";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
