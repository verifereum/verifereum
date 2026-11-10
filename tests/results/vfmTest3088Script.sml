Theory vfmTest3088[no_sig_docs]
Ancestors vfmTestDefs3088
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3088_0.nsv", "result3088_1.nsv", "result3088_2.nsv"];
val thyn = "vfmTestDefs3088";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
