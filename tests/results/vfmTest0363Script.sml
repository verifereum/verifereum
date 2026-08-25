Theory vfmTest0363[no_sig_docs]
Ancestors vfmTestDefs0363
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0363_0.nsv", "result0363_1.nsv", "result0363_2.nsv", "result0363_3.nsv", "result0363_4.nsv", "result0363_5.nsv", "result0363_6.nsv", "result0363_7.nsv", "result0363_8.nsv", "result0363_9.nsv", "result0363_10.nsv", "result0363_11.nsv", "result0363_12.nsv", "result0363_13.nsv", "result0363_14.nsv", "result0363_15.nsv", "result0363_16.nsv", "result0363_17.nsv"];
val thyn = "vfmTestDefs0363";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
