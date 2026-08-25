Theory vfmTest0968[no_sig_docs]
Ancestors vfmTestDefs0968
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0968_0.nsv", "result0968_1.nsv", "result0968_2.nsv", "result0968_3.nsv", "result0968_4.nsv", "result0968_5.nsv", "result0968_6.nsv", "result0968_7.nsv", "result0968_8.nsv", "result0968_9.nsv", "result0968_10.nsv", "result0968_11.nsv"];
val thyn = "vfmTestDefs0968";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
