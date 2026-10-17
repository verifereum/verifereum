Theory vfmTest0362[no_sig_docs]
Ancestors vfmTestDefs0362
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0362_0.nsv", "result0362_1.nsv", "result0362_2.nsv", "result0362_3.nsv", "result0362_4.nsv", "result0362_5.nsv", "result0362_6.nsv", "result0362_7.nsv", "result0362_8.nsv", "result0362_9.nsv", "result0362_10.nsv", "result0362_11.nsv", "result0362_12.nsv", "result0362_13.nsv", "result0362_14.nsv", "result0362_15.nsv", "result0362_16.nsv", "result0362_17.nsv", "result0362_18.nsv", "result0362_19.nsv", "result0362_20.nsv", "result0362_21.nsv"];
val thyn = "vfmTestDefs0362";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
