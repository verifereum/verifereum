Theory vfmTest0374[no_sig_docs]
Ancestors vfmTestDefs0374
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0374_0.nsv", "result0374_1.nsv", "result0374_2.nsv", "result0374_3.nsv", "result0374_4.nsv", "result0374_5.nsv", "result0374_6.nsv", "result0374_7.nsv", "result0374_8.nsv", "result0374_9.nsv", "result0374_10.nsv", "result0374_11.nsv", "result0374_12.nsv", "result0374_13.nsv", "result0374_14.nsv", "result0374_15.nsv", "result0374_16.nsv", "result0374_17.nsv", "result0374_18.nsv", "result0374_19.nsv"];
val thyn = "vfmTestDefs0374";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
