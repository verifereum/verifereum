Theory vfmTest0573[no_sig_docs]
Ancestors vfmTestDefs0573
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0573_0.nsv", "result0573_1.nsv", "result0573_2.nsv", "result0573_3.nsv", "result0573_4.nsv", "result0573_5.nsv", "result0573_6.nsv", "result0573_7.nsv"];
val thyn = "vfmTestDefs0573";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
