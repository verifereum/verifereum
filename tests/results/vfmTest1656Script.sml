Theory vfmTest1656[no_sig_docs]
Ancestors vfmTestDefs1656
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1656_0.nsv", "result1656_1.nsv", "result1656_2.nsv", "result1656_3.nsv", "result1656_4.nsv", "result1656_5.nsv", "result1656_6.nsv", "result1656_7.nsv", "result1656_8.nsv", "result1656_9.nsv", "result1656_10.nsv", "result1656_11.nsv", "result1656_12.nsv", "result1656_13.nsv", "result1656_14.nsv", "result1656_15.nsv", "result1656_16.nsv", "result1656_17.nsv", "result1656_18.nsv", "result1656_19.nsv"];
val thyn = "vfmTestDefs1656";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
