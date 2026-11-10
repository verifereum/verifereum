Theory vfmTest3099[no_sig_docs]
Ancestors vfmTestDefs3099
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3099_0.nsv", "result3099_1.nsv", "result3099_2.nsv", "result3099_3.nsv", "result3099_4.nsv", "result3099_5.nsv", "result3099_6.nsv", "result3099_7.nsv"];
val thyn = "vfmTestDefs3099";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
