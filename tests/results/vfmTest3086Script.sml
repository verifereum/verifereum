Theory vfmTest3086[no_sig_docs]
Ancestors vfmTestDefs3086
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3086_0.nsv", "result3086_1.nsv", "result3086_2.nsv", "result3086_3.nsv", "result3086_4.nsv", "result3086_5.nsv", "result3086_6.nsv", "result3086_7.nsv"];
val thyn = "vfmTestDefs3086";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
