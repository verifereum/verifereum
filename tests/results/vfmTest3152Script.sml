Theory vfmTest3152[no_sig_docs]
Ancestors vfmTestDefs3152
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3152_0.nsv", "result3152_1.nsv", "result3152_2.nsv", "result3152_3.nsv", "result3152_4.nsv", "result3152_5.nsv"];
val thyn = "vfmTestDefs3152";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
