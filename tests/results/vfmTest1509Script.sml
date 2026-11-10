Theory vfmTest1509[no_sig_docs]
Ancestors vfmTestDefs1509
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1509_0.nsv", "result1509_1.nsv", "result1509_2.nsv", "result1509_3.nsv", "result1509_4.nsv", "result1509_5.nsv", "result1509_6.nsv", "result1509_7.nsv", "result1509_8.nsv", "result1509_9.nsv", "result1509_10.nsv", "result1509_11.nsv", "result1509_12.nsv", "result1509_13.nsv", "result1509_14.nsv", "result1509_15.nsv", "result1509_16.nsv", "result1509_17.nsv", "result1509_18.nsv", "result1509_19.nsv", "result1509_20.nsv", "result1509_21.nsv"];
val thyn = "vfmTestDefs1509";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
