Theory vfmTest3119[no_sig_docs]
Ancestors vfmTestDefs3119
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3119_0.nsv", "result3119_1.nsv"];
val thyn = "vfmTestDefs3119";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
