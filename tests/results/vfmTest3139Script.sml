Theory vfmTest3139[no_sig_docs]
Ancestors vfmTestDefs3139
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3139_0.nsv", "result3139_1.nsv", "result3139_2.nsv", "result3139_3.nsv"];
val thyn = "vfmTestDefs3139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
