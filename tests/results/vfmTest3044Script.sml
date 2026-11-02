Theory vfmTest3044[no_sig_docs]
Ancestors vfmTestDefs3044
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3044_0.nsv", "result3044_1.nsv", "result3044_2.nsv", "result3044_3.nsv", "result3044_4.nsv", "result3044_5.nsv", "result3044_6.nsv"];
val thyn = "vfmTestDefs3044";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
