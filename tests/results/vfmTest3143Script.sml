Theory vfmTest3143[no_sig_docs]
Ancestors vfmTestDefs3143
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3143_0.nsv", "result3143_1.nsv", "result3143_2.nsv", "result3143_3.nsv"];
val thyn = "vfmTestDefs3143";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
