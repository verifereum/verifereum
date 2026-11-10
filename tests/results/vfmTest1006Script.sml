Theory vfmTest1006[no_sig_docs]
Ancestors vfmTestDefs1006
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1006_0.nsv", "result1006_1.nsv", "result1006_2.nsv", "result1006_3.nsv", "result1006_4.nsv", "result1006_5.nsv", "result1006_6.nsv", "result1006_7.nsv", "result1006_8.nsv", "result1006_9.nsv", "result1006_10.nsv", "result1006_11.nsv"];
val thyn = "vfmTestDefs1006";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
