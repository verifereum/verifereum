Theory vfmTest0139[no_sig_docs]
Ancestors vfmTestDefs0139
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0139_0.nsv", "result0139_1.nsv", "result0139_2.nsv", "result0139_3.nsv", "result0139_4.nsv", "result0139_5.nsv", "result0139_6.nsv", "result0139_7.nsv"];
val thyn = "vfmTestDefs0139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
