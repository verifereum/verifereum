Theory vfmTest0589[no_sig_docs]
Ancestors vfmTestDefs0589
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0589_0.nsv", "result0589_1.nsv", "result0589_2.nsv", "result0589_3.nsv", "result0589_4.nsv", "result0589_5.nsv", "result0589_6.nsv", "result0589_7.nsv", "result0589_8.nsv", "result0589_9.nsv", "result0589_10.nsv", "result0589_11.nsv", "result0589_12.nsv", "result0589_13.nsv", "result0589_14.nsv", "result0589_15.nsv"];
val thyn = "vfmTestDefs0589";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
