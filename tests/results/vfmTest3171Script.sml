Theory vfmTest3171[no_sig_docs]
Ancestors vfmTestDefs3171
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3171_0.nsv", "result3171_1.nsv", "result3171_2.nsv", "result3171_3.nsv", "result3171_4.nsv", "result3171_5.nsv"];
val thyn = "vfmTestDefs3171";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
