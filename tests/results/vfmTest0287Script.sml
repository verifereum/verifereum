Theory vfmTest0287[no_sig_docs]
Ancestors vfmTestDefs0287
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0287_0.nsv", "result0287_1.nsv", "result0287_2.nsv", "result0287_3.nsv", "result0287_4.nsv", "result0287_5.nsv", "result0287_6.nsv", "result0287_7.nsv", "result0287_8.nsv", "result0287_9.nsv", "result0287_10.nsv", "result0287_11.nsv", "result0287_12.nsv", "result0287_13.nsv", "result0287_14.nsv", "result0287_15.nsv", "result0287_16.nsv", "result0287_17.nsv", "result0287_18.nsv", "result0287_19.nsv"];
val thyn = "vfmTestDefs0287";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
