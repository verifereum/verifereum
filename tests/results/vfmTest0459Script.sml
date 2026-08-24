Theory vfmTest0459[no_sig_docs]
Ancestors vfmTestDefs0459
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0459_0.nsv", "result0459_1.nsv", "result0459_2.nsv", "result0459_3.nsv", "result0459_4.nsv", "result0459_5.nsv", "result0459_6.nsv", "result0459_7.nsv", "result0459_8.nsv", "result0459_9.nsv", "result0459_10.nsv", "result0459_11.nsv", "result0459_12.nsv", "result0459_13.nsv", "result0459_14.nsv", "result0459_15.nsv", "result0459_16.nsv", "result0459_17.nsv", "result0459_18.nsv", "result0459_19.nsv", "result0459_20.nsv", "result0459_21.nsv", "result0459_22.nsv", "result0459_23.nsv", "result0459_24.nsv", "result0459_25.nsv"];
val thyn = "vfmTestDefs0459";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
