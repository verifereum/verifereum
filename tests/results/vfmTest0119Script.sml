Theory vfmTest0119[no_sig_docs]
Ancestors vfmTestDefs0119
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0119_0.nsv", "result0119_1.nsv", "result0119_2.nsv", "result0119_3.nsv"];
val thyn = "vfmTestDefs0119";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
