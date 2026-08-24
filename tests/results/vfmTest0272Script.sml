Theory vfmTest0272[no_sig_docs]
Ancestors vfmTestDefs0272
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0272_0.nsv", "result0272_1.nsv", "result0272_2.nsv", "result0272_3.nsv", "result0272_4.nsv", "result0272_5.nsv", "result0272_6.nsv", "result0272_7.nsv", "result0272_8.nsv", "result0272_9.nsv", "result0272_10.nsv", "result0272_11.nsv", "result0272_12.nsv", "result0272_13.nsv", "result0272_14.nsv", "result0272_15.nsv", "result0272_16.nsv", "result0272_17.nsv", "result0272_18.nsv", "result0272_19.nsv"];
val thyn = "vfmTestDefs0272";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
