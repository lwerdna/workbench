extern void init();
extern void rotation();
extern void translation();
extern int unknown();

void function(void)
{
	init(0, 1, 0, 1);
	translation(1, 0);
	while(unknown())
	{
		if(unknown())
		{
			translation(1, 0);
			translation(2, 3);
		}
		else
		{
			rotation(0, 0, 90);
		}
	}
	return;
}
