Theory vfmTest0213[no_sig_docs]
Ancestors vfmTestDefs0213
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0213_0.nsv", "result0213_1.nsv", "result0213_2.nsv", "result0213_3.nsv", "result0213_4.nsv", "result0213_5.nsv", "result0213_6.nsv", "result0213_7.nsv", "result0213_8.nsv", "result0213_9.nsv", "result0213_10.nsv", "result0213_11.nsv", "result0213_12.nsv", "result0213_13.nsv", "result0213_14.nsv", "result0213_15.nsv", "result0213_16.nsv", "result0213_17.nsv", "result0213_18.nsv", "result0213_19.nsv", "result0213_20.nsv"];
val thyn = "vfmTestDefs0213";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
