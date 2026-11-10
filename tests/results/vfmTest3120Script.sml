Theory vfmTest3120[no_sig_docs]
Ancestors vfmTestDefs3120
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3120_0.nsv", "result3120_1.nsv", "result3120_2.nsv", "result3120_3.nsv", "result3120_4.nsv", "result3120_5.nsv", "result3120_6.nsv", "result3120_7.nsv"];
val thyn = "vfmTestDefs3120";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
